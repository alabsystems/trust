//! trust-mir-extract: Bridge from tRustc MIR to trust-types verification model
//!
//! Walks tRustc's Body<'tcx> and produces VerifiableFunction instances that
//! the downstream pipeline (trust_vcgen, trust-router) can operate on without
//! any rustc dependencies.
//!
//! Requires: #![feature(rustc_private)]
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: rustc_private + box_patterns needed when built standalone (targo --unverified build).
// When built as part of the compiler workspace (via x.py), the extern crates
// are resolved through Cargo.toml path dependencies.
#![feature(rustc_private)]
// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): the unit tests run the compiler in
// process; their binary captures its scheduler at native entry.
#![cfg_attr(
    all(test, any(target_os = "linux", target_os = "macos")),
    feature(test, custom_test_frameworks, exitcode_exit_method)
)]
#![cfg_attr(
    all(test, any(target_os = "linux", target_os = "macos")),
    test_runner(crate::native_test_entry::main)
)]
#![feature(register_tool)]
#![register_tool(trust)]
// Upstream 1.101: `box_patterns` was removed; deref patterns replace it.
#![feature(deref_patterns)]
// This rustc-private bridge intentionally uses compiler-internal features.
#![allow(internal_features)]
#![allow(unused_extern_crates)]
#![allow(unknown_lints)]
// Trust: 1.99 added the `rustc::symbol_intern_string_literal` internal lint
// (prefer pre-interned `sym::` over `Symbol::intern("...")`). Trust's #[cfg(test)]
// fixtures intern short ad-hoc predicate strings ("x > 0", ...) that have no
// pre-interned symbol; allow it crate-wide (only test code interns literals).
#![allow(rustc::symbol_intern_string_literal)]
#![allow(rustc::usage_of_ty_tykind)]
#![allow(rustc::usage_of_qualified_ty)]
#![allow(rustc::default_hash_types)]
// dead_code audit: crate-level suppression removed

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_attr_ir;
extern crate rustc_ast_ir;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): the unit-test binary's native entry.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
#[path = "../tests/support/native_test_entry.rs"]
mod native_test_entry;

// Research-only MIR call-graph implementation. The production interprocedural
// pipeline uses the shared `trust-types`/`trust-vcgen` graph; this second graph
// has no non-test caller. Compile its tests without carrying a redundant graph
// implementation in every trustc build.
#[cfg(test)]
mod call_graph;
// Research-only feasibility transform for a synthetic, fuel-shaped Cell
// counter. It is deliberately excluded from production builds: the real
// compiler has neither a sound automatic cluster/reference discovery contract
// nor a u32-to-inductive-fuel refinement witness. Keeping this test-only makes
// the remaining production extraction gap explicit instead of advertising an
// unwired public API.
#[cfg(test)]
mod cell_threading;
pub mod contract_assumption_gate;
/// Trust (LANE 1): the CTFE FREEZE — "this thread is inside `mir_built`, so forcing
/// const-evaluation would close a rustc query cycle".
///
/// This extractor has two callers with opposite hazard profiles, and until now only one of them
/// was reasoned about:
///
///   * the VERIFIER (`rustc_mir_transform::trust_verify`, at `optimized_mir` time) — CTFE here is
///     both safe and load-bearing: it is how a const operand becomes a known value in an
///     obligation instead of an opaque scalar. Nothing below may weaken that lane, and nothing
///     does: the freeze is never entered on that path.
///
///   * the trust-ir producer's MIR-side ORACLE (`trust_thir_lower::differential` /
///     `mir_differential`), which runs INSIDE the `mir_built` query hook
///     (`rustc_mir_build::builder::build_mir_inner_impl`). Every `mir::Const::Unevaluated`
///     operand it evaluates demands `mir_for_ctfe` -> `mir_borrowck` of the const, and borrowck
///     descends into the const's nested closures, demanding THEIR `mir_built`. For a
///     self-referential const pair that closes a cycle on rustc's own query stack — a hard
///     `error[E0391]`, i.e. `-Ztrust-ir-lower` turning a program vanilla rustc compiles into a
///     failing one. Measured on `core::task::wake`'s `RawWaker::NOOP`:
///         const NOOP: RawWaker = { const VTABLE: VT = VT::new(|_| RawWaker::NOOP, ..); .. };
///     one of the three E0391 cycles that made `library/core` produce ZERO obligations.
///
/// So one half of the rule is a property of WHERE we are, not of what we are looking at, and that
/// half is entered once at the hook boundary rather than sprinkled over shapes. When a helper does
/// decline it returns `None`, which is this extractor's existing, well-defined "value unavailable"
/// answer (the same one a generic const gets): the operand stays opaque, the differential records
/// incapacity, and no body reads as agreed on a value nobody computed.
///
/// **`frozen()` is NOT on its own the decline predicate — read
/// `convert::frozen_ctfe_may_reach_local_body` before adding a call site.** Being inside
/// `mir_built` is necessary for the hazard but not sufficient: the cycle needs the const's CTFE to
/// actually demand a LOCAL `mir_built`. The first form of this guard skipped that second question
/// and keyed on the MIR SPELLING instead (`Const::Unevaluated` vs `Const::Val`), which declined
/// every foreign assoc const — `i8::MAX`, `u8::MIN`, `Assume::SAFETY` — whose provider is the
/// metadata decoder and which can demand no local query at all. MEASURED cost on the 2000-file ui
/// sample: **132 Agreed rows**, against **zero** prevented compile failures on that corpus
/// (`file_outcomes` was byte-identical with the freeze present and absent). The sibling THIR
/// producer lane never had this bug — it has always keyed on `def_id.is_local()` — so the two
/// sides of one differential disagreed by construction on every non-local const.
///
/// Thread-local, matching `trust_thir_lower`'s `LOWERING_BODIES`: rustc builds MIR on parallel
/// worker threads and each owns its own query stack, so a global would both mis-fire and
/// mis-decline.
pub mod ctfe_reentrancy {
    mod closed_layout_memo;
    mod freeze_frames;
    use closed_layout_memo::{ClosedLayoutMemo, ProjectionRhsPolicy};
    use freeze_frames::{FrameToken, FreezeFrames};
    use std::cell::{Cell, RefCell};

    use rustc_middle::ty::{
        self, TyCtxt, TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitableExt, Upcast,
    };
    use rustc_span::def_id::{DefId, LocalDefId};

    thread_local! {
        /// One owned frame per live [`Freeze`] on this thread, newest last. A guard may be
        /// explicitly dropped before an inner guard, so private token identity, not stack
        /// position, selects the frame removed by Drop. Trust (fix11, L2): a frame also
        /// records the body it is held for —
        /// `Some(def)` from [`enter_building`] (the `mir_built` hook and the `trust_ir_of`
        /// lowering), `None` from [`enter`] (a holder that does not say) — because whether a
        /// leaf constant may be evaluated inside the freeze depends on which bodies are being
        /// lowered on this thread ([`evaluation_admitted_here`]).
        static FREEZE_FRAMES: RefCell<FreezeFrames<LocalDefId>> = const { RefCell::new(FreezeFrames::new()) };
        // A return to an identical stack is still a new policy epoch. Overflow
        // disables cross-query reuse permanently rather than wrapping an identity.
        static FREEZE_EPOCH: Cell<Option<u64>> = const { Cell::new(Some(0)) };
    }

    fn freeze_epoch() -> Option<u64> {
        FREEZE_EPOCH.with(Cell::get)
    }

    /// RAII: the freeze is released even if the producer returns early or unwinds.
    pub struct Freeze {
        frame: FrameToken,
    }

    /// Enter the freeze for the current thread. Held for as long as the returned value lives.
    /// The frame names no body, so no constant is evaluated while it is held
    /// ([`evaluation_admitted_here`]): a holder that lowers a body uses [`enter_building`].
    #[must_use]
    pub fn enter() -> Freeze {
        FREEZE_EPOCH.with(|e| e.set(e.get().and_then(|n| n.checked_add(1))));
        let frame = FREEZE_FRAMES.with(|f| f.borrow_mut().enter(None));
        Freeze { frame }
    }

    /// Enter the freeze for the current thread while lowering the body `def` (the `mir_built`
    /// hook and the `trust_ir_of` query). Same as [`enter`], and the frame records `def` for
    /// as long as the returned value lives.
    #[must_use]
    pub fn enter_building(def: LocalDefId) -> Freeze {
        FREEZE_EPOCH.with(|e| e.set(e.get().and_then(|n| n.checked_add(1))));
        let frame = FREEZE_FRAMES.with(|f| f.borrow_mut().enter(Some(def)));
        Freeze { frame }
    }

    impl Drop for Freeze {
        fn drop(&mut self) {
            FREEZE_EPOCH.with(|e| e.set(e.get().and_then(|n| n.checked_add(1))));
            FREEZE_FRAMES.with(|f| {
                f.borrow_mut().remove(&self.frame);
            });
        }
    }

    /// Must a forced const-evaluation be declined on this thread right now?
    #[must_use]
    pub fn frozen() -> bool {
        FREEZE_FRAMES.with(|f| !f.borrow().is_empty())
    }

    /// May a constant whose whole CTFE closure is leaf ([`ctfe_closure_is_leaf`]) be evaluated
    /// on this thread right now? Always outside the freeze. Inside it, only when every frame
    /// names a body ([`enter_building`]) and none of those bodies could be in a leaf closure
    /// ([`may_be_leaf_body`]): a frame lowering one could be a query of the very closure
    /// being evaluated (the L2 note below). A frame lowering an ordinary `fn`, a closure, a
    /// `static`, an inline `const`, or a constant that is not primitive-typed or not
    /// leaf-shaped cannot be. `false` is the fail-closed answer.
    #[must_use]
    pub fn evaluation_admitted_here(tcx: TyCtxt<'_>) -> bool {
        // A snapshot: the check below asks queries, and a query may enter and leave a freeze.
        enum Snapshot {
            Admitted,
            Declined,
            One(LocalDefId),
            Many(Vec<LocalDefId>),
        }
        let snapshot = FREEZE_FRAMES.with(|f| {
            let frames = f.borrow();
            match frames.len() {
                0 => Snapshot::Admitted,
                1 => match frames.iter().next() {
                    Some(Some(def)) => Snapshot::One(*def),
                    _ => Snapshot::Declined,
                },
                count => {
                    let mut defs = Vec::with_capacity(count);
                    for frame in frames.iter() {
                        let Some(def) = *frame else {
                            return Snapshot::Declined;
                        };
                        defs.push(def);
                    }
                    Snapshot::Many(defs)
                }
            }
        });
        match snapshot {
            Snapshot::Admitted => true,
            Snapshot::Declined => false,
            Snapshot::One(def) => !may_be_leaf_body(tcx, def),
            Snapshot::Many(defs) => defs.into_iter().all(|def| !may_be_leaf_body(tcx, def)),
        }
    }

    /// Could `def` be a body of some leaf closure ([`ctfe_closure_is_leaf`])? An
    /// over-approximation read from the item's kind, its `type_of` (computed by the `typeck`
    /// that ran before its MIR was built; an anonymous constant's is read off its HIR parent)
    /// and its HIR: a closure's bodies are leaf constants — `const` / associated `const` /
    /// anonymous constants of primitive scalar type whose HIR passes [`leaf_shape`], of which
    /// [`syntactically_leaf_shaped`] is the query-free superset — and the bodies of the layout
    /// queries a leaf body may call: `core::mem::size_of` / `align_of`,
    /// `SizedTypeProperties::SIZE` / `ALIGN` and the `size_of` / `align_of` intrinsics they
    /// call (local only while `core` itself is compiled; the intrinsics have no body today).
    /// Anything else answers `false`: no closure can contain it.
    fn may_be_leaf_body(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
        use rustc_attr_ir::lang_items::LangItem;
        use rustc_hir::def::DefKind;
        let did = def.to_def_id();
        match tcx.def_kind(def) {
            DefKind::Fn => {
                is_layout_query_fn(tcx, did)
                    || tcx.intrinsic(did).is_some_and(|intrinsic| {
                        matches!(intrinsic.name, rustc_span::sym::size_of | rustc_span::sym::align_of)
                    })
            }
            DefKind::AssocConst { .. }
                if tcx.is_lang_item(did, LangItem::SizeOf)
                    || tcx.is_lang_item(did, LangItem::AlignOf) =>
            {
                true
            }
            DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::AnonConst => {
                let t = tcx.type_of(def).instantiate_identity().skip_norm_wip();
                let typed_as_leaf = is_primitive_scalar(t)
                    || matches!(t.kind(), ty::Param(_) | ty::Alias(..) | ty::Infer(_))
                    || t.references_error();
                typed_as_leaf
                    && tcx.hir_maybe_body_owned_by(def).is_none_or(|body| {
                        let mut budget = LEAF_MAX_EXPRS;
                        syntactically_leaf_shaped(tcx, &body.value, &mut budget)
                    })
            }
            _ => false,
        }
    }

    /// The leaf grammar of [`leaf_shape`] read from HIR alone, without its inertness and type
    /// checks: a superset of the bodies `leaf_shape` admits, so a body this answers `false`
    /// for is in no leaf closure. Past `budget` expressions it answers `true`, the side that
    /// keeps a frame forbidding evaluation.
    fn syntactically_leaf_shaped(
        tcx: TyCtxt<'_>,
        e: &rustc_hir::Expr<'_>,
        budget: &mut usize,
    ) -> bool {
        use rustc_hir::def::{DefKind, Res};
        use rustc_hir::{ExprKind, QPath, UnOp};
        if *budget == 0 {
            return true;
        }
        *budget -= 1;
        match e.kind {
            ExprKind::Lit(_) | ExprKind::Path(QPath::TypeRelative(..)) => true,
            ExprKind::Path(QPath::Resolved(_, path)) => {
                matches!(path.res, Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, _))
            }
            ExprKind::Cast(inner, _)
            | ExprKind::Unary(UnOp::Neg | UnOp::Not, inner)
            | ExprKind::DropTemps(inner) => syntactically_leaf_shaped(tcx, inner, budget),
            ExprKind::Binary(_, l, r) => {
                syntactically_leaf_shaped(tcx, l, budget) && syntactically_leaf_shaped(tcx, r, budget)
            }
            ExprKind::Block(block, None) => {
                block.stmts.is_empty()
                    && block.expr.is_some_and(|tail| syntactically_leaf_shaped(tcx, tail, budget))
            }
            ExprKind::Call(callee, []) => matches!(
                callee.kind,
                ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Def(DefKind::Fn, did) if is_layout_query_fn(tcx, did))
            ),
            _ => false,
        }
    }

    // ---- THE REVEAL FUNNEL: what a type query asked inside `mir_built` may demand ----
    //
    // Inside `mir_built` the producer and its MIR oracle run inside a query the type system
    // reaches (`type_of(opaque)` -> `mir_borrowck` -> `mir_built`), so the async-layout
    // design's rule holds for every type query they ask: it must not reveal an opaque type
    // (revealing demands `type_of` of the opaque, i.e. borrowck of its defining body — the
    // body under construction, or the one enclosing it) and must not read a coroutine's
    // MIR. Two kinds of question, two answers:
    //
    //   * a question with an ANALYSIS-mode answer (`needs_drop`, `Copy`, `Sized`,
    //     normalization) is asked in the typing mode vanilla `mir_build` itself asks it in
    //     ([`analysis_env_if_frozen`]): opaques stay rigid, nothing is revealed, and the
    //     answer is the one the built MIR was built from — in a crate with no opaque of its
    //     own. In one that declares an opaque that mode still LEAKS the opaque's auto traits
    //     through an impl's where-clause, and the question is answered leak-free instead
    //     ([`leak_free_typing_mode`], OPAQUE-IMPL-WHERE-LEAK-1, below);
    //   * a question only the CODEGEN mode answers (`layout_of`, `Instance::try_resolve`, an
    //     auto trait such as `Freeze`) is asked only of types
    //     [`layout_query_is_reentrant_safe_deep`] admits, and a resolution only of a trait
    //     reference whose selection [`select_reveal_free`] walks; any other question is
    //     declined with the site's existing "unknown" answer.

    /// `te` with its typing mode replaced, inside `mir_built`, by the non-body analysis
    /// mode `rustc_mir_build` builds MIR in (`builder/mod.rs`, `TypingMode::
    /// non_body_analysis`). Outside `mir_built` — the verifier at `optimized_mir` time — it
    /// is `te` unchanged.
    #[must_use]
    pub fn analysis_env_if_frozen<'tcx>(te: ty::TypingEnv<'tcx>) -> ty::TypingEnv<'tcx> {
        if frozen() {
            ty::TypingEnv::new(te.param_env, ty::TypingMode::non_body_analysis())
        } else {
            te
        }
    }

    // ---- AUTO-TRAIT LEAKAGE AND WHERE-CLAUSES: the analysis mode is not reveal-free ----
    //                                              (OPAQUE-IMPL-WHERE-LEAK-1)
    //
    // `non_body_analysis` keeps an opaque RIGID, but it still LEAKS the opaque's auto traits:
    // an auto-trait goal on an opaque this mode may not define is proved from the opaque's
    // hidden type (`rustc_trait_selection` `select/mod.rs`, the `AutoImplCandidate`
    // constituents: `type_of_opaque`), which borrow-checks the opaque's defining body. Nothing
    // in the type being asked about has to name the opaque: a NORMALIZATION selects an impl,
    // and the impl's WHERE-CLAUSE can (`impl Prim for u8 where W: Send`, `struct W { x: Tait }`).
    // Measured (2026-10-14, the stage 1 of `integ/fix10` `425f2192be`): `<u8 as Prim>::Storage`
    // normalized from inside `mir_built` of `Tait`'s defining fn `define` -> "`W: Send`" ->
    // "computing type of opaque `Tait`" -> "borrow-checking `define`" -> E0391, on code stock
    // rustc accepts. Stock never asks it there; rustc's DAG of auto-trait leakage ("which
    // enforces a DAG between the functions requiring the auto trait bounds") holds only while
    // nothing inside `mir_built` asks a question stock does not.
    //
    // The CODEGEN mode is worse: it reveals every opaque a selection meets, and a selection
    // meets the where-clauses of every impl it confirms (`impl Prim for u8 where Tait: Debug`
    // is normalized to the hidden type there, no auto trait needed). Same cycle, through
    // `codegen_select_candidate` (`resolve_projection` below, `Instance::try_resolve`).
    //
    // The merged policies remain distinct. General guarded analysis uses
    // OpaqueAnalysis, retaining its builtin/layout-sensitive refusal scope.
    // Complete-probe codegen selection uses OpaqueBoundsOnly with the next
    // solver and the old solver's definable-local-opaque Typeck context. The
    // incoming selected-projection fallback keeps its narrower OpaqueAnalysis
    // route. Neither selection route falls back to the other after refusal;
    // their canonical/cache identities remain separate.
    //
    // The Typeck fallback makes local opaques definable so implicit auto traits
    // are ambiguous rather than read from their hidden types. OpaqueAnalysis
    // and OpaqueBoundsOnly instead retain rigid identities and declared bounds.
    //
    //   * an ANALYSIS-mode question (normalization, `Copy`, `Sized`, `needs_drop`) is ANSWERED
    //     in the leak-free mode, never in the analysis mode: on an `InferCtxt` this module owns
    //     ([`try_normalize_leak_free`], [`trait_holds_leak_free`]) — so an ambiguity is a
    //     DECLINE (`None` / `false`), never the query normalizer's "unexpected ambiguity"
    //     delayed bug, and a hidden type the solver proposed for a definable opaque is a
    //     decline too (the answer would rest on a guess) — and `needs_drop` is this module's
    //     own walk over the same components ([`needs_drop_leak_free`]): rustc's query reads
    //     an ADT's fields through `adt_drop_tys`, computed in that ADT's own LEAKING mode;
    //   * a CODEGEN-mode selection is first WALKED in the leak-free mode
    //     ([`select_reveal_free`]): every obligation the selection and its nested selections
    //     make must hold there and NAME no opaque and no coroutine, or the codegen-mode
    //     question is declined with its site's existing "unknown" answer.
    //
    // Every `InferCtxt` built here has its proposed hidden types TAKEN on every path: one
    // dropped with a non-empty opaque-type storage in the typeck mode is a delayed bug
    // (`rustc_infer` `impl Drop for InferCtxt`).

    fn local_opaques<'tcx>(tcx: TyCtxt<'tcx>) -> &'tcx ty::List<LocalDefId> {
        let slice = tcx.hir_crate_items(()).opaque_slice();
        if slice.is_empty() { ty::List::empty() } else { tcx.mk_local_def_ids(slice) }
    }

    /// The complete-probe guard's mode: rigid opaque bounds with the next
    /// solver, or the old solver's definable-local-opaque context. General
    /// analysis passes the distinct OpaqueAnalysis mode explicitly.
    #[must_use]
    pub(crate) fn leak_free_typing_mode<'tcx>(tcx: TyCtxt<'tcx>) -> ty::TypingMode<'tcx> {
        if tcx.next_trait_solver_globally() {
            // Preserve declared bounds without inferring a hidden type or
            // leaking an opaque's undeclared auto traits. Its canonical/cache
            // identity is distinct from ordinary non-body analysis.
            ty::TypingMode::OpaqueBoundsOnly
        } else {
            ty::TypingMode::Typeck { defining_opaque_types_and_generators: local_opaques(tcx) }
        }
    }

    /// Does this crate declare any opaque type? Without one there is nothing to leak, so
    /// the wrappers retain the ordinary `non_body_analysis` path.
    #[must_use]
    pub(crate) fn crate_has_local_opaques(tcx: TyCtxt<'_>) -> bool {
        !tcx.hir_crate_items(()).opaque_slice().is_empty()
    }

    /// Must a type question asked right now be asked leak-free? Inside `mir_built`, in a crate
    /// that declares an opaque type.
    #[must_use]
    pub fn leak_free_required(tcx: TyCtxt<'_>) -> bool {
        frozen() && crate_has_local_opaques(tcx)
    }

    /// Normalization as a question asked inside `mir_built` may ask it: outside the freeze,
    /// `te` unchanged (rustc's query); inside it, the analysis mode when this crate declares no
    /// opaque, else [`try_normalize_leak_free`] — and in either mode only when no constant the
    /// value names would be evaluated there ([`non_leaf_constant_if_frozen`], fix11
    /// CTFE-IN-MIR-BUILT-1: the normalizer evaluates every constant it meets, and inside the
    /// freeze that is CTFE on this thread's query stack). `None` is every caller's "unknown".
    #[must_use]
    pub fn try_normalize_unrevealed<'tcx, T>(
        tcx: TyCtxt<'tcx>,
        te: ty::TypingEnv<'tcx>,
        value: T,
    ) -> Option<T>
    where
        T: TypeFoldable<TyCtxt<'tcx>>,
    {
        if non_leaf_constant_if_frozen(tcx, &value).is_some() {
            return None;
        }
        if leak_free_required(tcx) {
            try_normalize_leak_free(tcx, te.param_env, value)
        } else {
            tcx.try_normalize_erasing_regions(
                analysis_env_if_frozen(te),
                ty::Unnormalized::new_wip(value),
            )
            .ok()
        }
    }

    /// Type-specific normalization with the layout funnel's existing selected-RHS
    /// recovery. OpaqueAnalysis cannot evaluate even an admitted leaf alias constant;
    /// a monomorphic projection may instead read its selected impl's written value
    /// and evaluate only the leaf constants already admitted by the funnel.
    ///
    /// Keep ordinary normalization first and all its ambiguity/opaque checks. The
    /// fallback is frozen, empty-environment and projection-only, returns an alias-free
    /// concrete value, and carries the same recursive argument/depth gates as layout.
    /// It does not enable CTFE in OpaqueAnalysis or change the generic normalizer.
    #[must_use]
    pub fn try_normalize_ty_unrevealed<'tcx>(
        tcx: TyCtxt<'tcx>,
        te: ty::TypingEnv<'tcx>,
        value: ty::Ty<'tcx>,
    ) -> Option<ty::Ty<'tcx>> {
        let normalized = try_normalize_unrevealed(tcx, te, value);
        if !frozen()
            || !te.param_env.is_empty()
            || normalized.is_some_and(|ty| !ty.has_aliases())
        {
            return normalized;
        }
        let ty::Alias(_, alias) = value.kind() else { return normalized };
        // OpaqueAnalysis may have exposed an array while retaining its length alias.
        // That partial result is not a completed projection: the bounded reader must
        // admit the entire written RHS, including its leaf constants, or decline.
        read_monomorphic_projection(tcx, *alias, 0)
    }

    /// The `InferCtxt` a leak-free question is answered on, and the environment it is asked
    /// in: `param_env` with one clause added, `'?0: 'static` on a fresh region variable of that
    /// `InferCtxt`. No goal is selected from it (only a trait or projection clause is a
    /// candidate), and regions are ignored here.
    ///
    /// The clause keeps every goal asked under this environment OUT of the old solver's GLOBAL
    /// selection and evaluation caches (OPAQUE-IMPL-WHERE-LEAK-1, residual (b), measured
    /// 2026-10-15). The previous all-definable Typeck policy keyed a goal that names no opaque
    /// by the typing mode with the defining set ERASED (`InferCtxt::typing_env`), sharing stock
    /// typeck's `non_body_analysis` key. A leak-free AMBIGUITY was therefore WRITTEN where stock reads —
    /// `Wrap2<u8>: Send` (a field holds `Tait`), asked while `define_rpit` was being built,
    /// was read back by the specialization winnowing of a later typeck, which could then not
    /// drop the specializing impl and reported E0283 on code stock rustc accepts
    /// (`tests/ui/trust/async-layout-no-cycle/impl_where_leak_cache_poison.rs`) — and a
    /// leaking answer stock had cached could be READ, making the leak-free answer
    /// order-dependent. rustc keeps a goal whose environment carries an inference variable in
    /// the asking `InferCtxt`'s own caches (`SelectionContext::can_use_global_caches`), and the
    /// canonical `evaluate_obligation` query that fulfillment's fast path asks re-creates the
    /// variable from its canonical input, so the same holds inside it. `OpaqueAnalysis` now
    /// also retains its own typing-env/canonical key and disables the old solver's global
    /// caches. Keep this independent marker guard as well.
    // Trust: callers choose the retained policy explicitly. General analysis
    // passes OpaqueAnalysis; complete-probe codegen selection passes the local
    // BoundsOnly/old-Typeck policy. Never erase or alias these cache identities.
    fn leak_free_infcx<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        typing_mode: ty::TypingMode<'tcx>,
    ) -> (rustc_infer::infer::InferCtxt<'tcx>, ty::ParamEnv<'tcx>) {
        use rustc_infer::infer::TyCtxtInferExt;
        // This environment was normalized in another typing mode. Rigid aliases from that
        // mode must be normalized again rather than treated as irreducible here.
        let param_env = ty::set_aliases_to_non_rigid(tcx, param_env).skip_norm_wip();
        let infcx = tcx.infer_ctxt().ignoring_regions().build(typing_mode);
        let local = infcx.next_region_var(rustc_infer::infer::RegionVariableOrigin::Misc(
            rustc_span::DUMMY_SP,
        ));
        let marker: ty::Clause<'tcx> =
            ty::ClauseKind::RegionOutlives(ty::OutlivesClause(local, tcx.lifetimes.re_static))
                .upcast(tcx);
        let param_env = ty::ParamEnv::new(tcx, param_env.caller_bounds().chain([marker]));
        (infcx, param_env)
    }

    /// Every free region of `value` (erased ones included) a fresh region variable of `infcx`,
    /// as the query normalizer's canonicalization would make it.
    fn with_region_vars<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
        infcx: &rustc_infer::infer::InferCtxt<'tcx>,
        value: T,
    ) -> T {
        ty::fold_regions(infcx.tcx, value, |r, _| {
            if r.is_bound() {
                r
            } else {
                infcx.next_region_var(rustc_infer::infer::RegionVariableOrigin::Misc(
                    rustc_span::DUMMY_SP,
                ))
            }
        })
    }

    /// Did the solver propose a hidden type for a definable opaque? Takes them, which every
    /// `InferCtxt` of this module must do before it is dropped (see the section comment).
    fn proposed_hidden_type(infcx: &rustc_infer::infer::InferCtxt<'_>) -> bool {
        !infcx.take_opaque_types().is_empty()
    }

    /// The alias kinds a normalization SELECTS an impl for (an opaque the analysis mode keeps
    /// rigid is not one of them).
    const NORMALIZABLE: ty::TypeFlags = ty::TypeFlags::HAS_TY_PROJECTION
        .union(ty::TypeFlags::HAS_TY_FREE_ALIAS)
        .union(ty::TypeFlags::HAS_TY_INHERENT)
        .union(ty::TypeFlags::HAS_CONST_ALIAS);

    /// `try_normalize_erasing_regions` that cannot leak a local opaque's auto traits: `None`
    /// when the normalization is ambiguous (an auto-trait goal on a local opaque, among
    /// others), fails, leaves an inference variable, or proposed a hidden type. `Some` is the
    /// region-erased normal form the analysis mode computes when it does not leak.
    #[must_use]
    pub(crate) fn try_normalize_leak_free<'tcx, T>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, value: T,
    ) -> Option<T> where T: TypeFoldable<TyCtxt<'tcx>> {
        try_normalize_leak_free_in_mode(tcx, param_env, value, ty::TypingMode::OpaqueAnalysis)
    }

    #[cfg(test)]
    pub(crate) fn try_normalize_bounds_only_for_test<'tcx, T>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, value: T,
    ) -> Option<T> where T: TypeFoldable<TyCtxt<'tcx>> {
        try_normalize_leak_free_in_mode(tcx, param_env, value, leak_free_typing_mode(tcx))
    }

    fn try_normalize_leak_free_in_mode<'tcx, T>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        value: T,
        typing_mode: ty::TypingMode<'tcx>,
    ) -> Option<T>
    where
        T: TypeFoldable<TyCtxt<'tcx>>,
    {
        use rustc_trait_selection::traits::{ObligationCause, ObligationCtxt};
        let value = ty::set_aliases_to_non_rigid(tcx, value).skip_norm_wip();
        if !value.has_type_flags(NORMALIZABLE) {
            return Some(tcx.erase_and_anonymize_regions(value));
        }
        if value.has_escaping_bound_vars() || value.has_non_region_infer() || param_env.has_infer()
        {
            return None;
        }
        let (infcx, param_env) = leak_free_infcx(tcx, param_env, typing_mode);
        let normalized = {
            let value = with_region_vars(&infcx, value);
            let ocx = ObligationCtxt::new(&infcx);
            // `deeply_normalize`, not `normalize`: under `-Znext-solver` the latter normalizes
            // nothing eagerly. Either solver's ambiguity is an `Err` here.
            let normalized = ocx
                .deeply_normalize(
                    &ObligationCause::dummy(),
                    param_env,
                    ty::Unnormalized::new_wip(value),
                )
                .ok();
            normalized.filter(|_| ocx.evaluate_obligations_error_on_ambiguity().no_errors())
        };
        let defined = proposed_hidden_type(&infcx);
        let normalized = infcx.deeply_resolve_via_unification_table(normalized.filter(|_| !defined)?);
        if normalized.has_non_region_infer() {
            return None;
        }
        Some(tcx.erase_and_anonymize_regions(normalized))
    }

    /// Does `ty: trait_def_id` hold, modulo regions, decided without leaking a local opaque's
    /// auto traits? `false` — the "not known to hold" answer — when the goal is ambiguous,
    /// fails, or rests on a proposed hidden type. For `Copy` and `Sized`, whose impls and
    /// field obligations can reach an impl where-clause naming an auto trait of a local
    /// opaque exactly as a normalization can.
    #[must_use]
    pub fn trait_holds_leak_free<'tcx>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, ty: ty::Ty<'tcx>,
        trait_def_id: rustc_span::def_id::DefId,
    ) -> bool {
        trait_holds_leak_free_in_mode(tcx, param_env, ty, trait_def_id, ty::TypingMode::OpaqueAnalysis)
    }

    #[cfg(test)]
    pub(crate) fn trait_holds_bounds_only_for_test<'tcx>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, ty: ty::Ty<'tcx>,
        trait_def_id: rustc_span::def_id::DefId,
    ) -> bool {
        trait_holds_leak_free_in_mode(tcx, param_env, ty, trait_def_id, leak_free_typing_mode(tcx))
    }

    fn trait_holds_leak_free_in_mode<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        ty: ty::Ty<'tcx>,
        trait_def_id: rustc_span::def_id::DefId,
        typing_mode: ty::TypingMode<'tcx>,
    ) -> bool {
        use rustc_trait_selection::traits::{ObligationCause, ObligationCtxt};
        let ty = ty::set_aliases_to_non_rigid(tcx, ty).skip_norm_wip();
        if ty.has_escaping_bound_vars() || ty.has_non_region_infer() || param_env.has_infer() {
            return false;
        }
        let (infcx, param_env) = leak_free_infcx(tcx, param_env, typing_mode);
        let holds = {
            let ty = with_region_vars(&infcx, ty);
            let ocx = ObligationCtxt::new(&infcx);
            ocx.register_bound(ObligationCause::dummy(), param_env, ty, trait_def_id);
            ocx.evaluate_obligations_error_on_ambiguity().no_errors()
        };
        let defined = proposed_hidden_type(&infcx);
        holds && !defined
    }

    /// `needs_drop` decided without a question that can leak a local opaque's auto traits.
    ///
    /// rustc's own `needs_drop` cannot be asked here in ANY typing mode: it walks an ADT's
    /// fields through `adt_drop_tys`, a query computed in that ADT's OWN analysis environment
    /// (`rustc_ty_utils::needs_drop`), which asks `Copy` of each component — a user `impl Copy
    /// for X where W: Send` confirms `W: Send` — and normalizes each field —
    /// `<u8 as Prim>::Storage` confirms `Wrap<u8>: Send` — in the leaking mode, whatever
    /// environment the outer question was keyed by (`impl_where_leak_copy_in_drop.rs`). This
    /// is the same walk as rustc's `NeedsDropTypes` over the same components
    /// (`needs_drop_components`), with every `Copy` goal decided by [`trait_holds_leak_free`]
    /// and every alias by [`try_normalize_leak_free`], and an ADT's fields read with `type_of`
    /// (no query computes them). FOREIGN ADTs are walked as local ones: `Peekable<Local>`'s
    /// field `<Local as Iterator>::Item` selects a local impl.
    ///
    /// `true` — "may need drop", every caller's fail-closed side — for an alias that does not
    /// normalize leak-free, a type naming a constant that may not be evaluated inside
    /// `mir_built` ([`non_leaf_constant_if_frozen`], asked before the normalization would
    /// evaluate it: fix11 CTFE-IN-MIR-BUILT-1), a parameter, placeholder or inference variable
    /// not known `Copy`, a coroutine (rustc answers the same without reading its MIR), a
    /// `dyn`, an error, and a walk past its budget. A `Copy` goal the leak-free mode cannot decide (ambiguous, say,
    /// on a where-clause naming a local opaque) walks the type's components instead: a type
    /// whose `Copy` impl holds has no component that needs drop, so the answer only moves
    /// toward `true`.
    #[must_use]
    pub fn needs_drop_leak_free<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> bool {
        const MAX_TYPES: usize = 512;
        let Some(copy) = tcx.lang_items().copy_trait() else {
            return true;
        };
        let mut seen: rustc_data_structures::fx::FxHashSet<ty::Ty<'tcx>> = Default::default();
        let mut stack = vec![tcx.erase_and_anonymize_regions(ty)];
        while let Some(ty) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > MAX_TYPES {
                return true;
            }
            let ty = if ty.has_type_flags(NORMALIZABLE) {
                if non_leaf_constant_if_frozen(tcx, &ty).is_some() {
                    return true;
                }
                let Some(norm) = try_normalize_leak_free(tcx, param_env, ty) else {
                    return true;
                };
                norm
            } else {
                ty
            };
            let Ok(components) = rustc_middle::ty::util::needs_drop_components(tcx, ty) else {
                return true;
            };
            for component in components {
                match *component.kind() {
                    ty::Coroutine(..) | ty::CoroutineWitness(..) => return true,
                    ty::UnsafeBinder(bound) => {
                        stack.push(tcx.instantiate_bound_regions_with_erased(bound.into()));
                    }
                    _ if trait_holds_leak_free(tcx, param_env, component, copy) => {}
                    ty::Closure(_, args) => stack.extend(args.as_closure().upvar_tys()),
                    ty::CoroutineClosure(_, args) => {
                        stack.extend(args.as_coroutine_closure().upvar_tys());
                    }
                    ty::Adt(def, args) => {
                        if def.is_manually_drop() {
                            continue;
                        }
                        if def.destructor(tcx).is_some() {
                            return true;
                        }
                        if def.is_union() {
                            continue;
                        }
                        for field in def.all_fields() {
                            stack.push(tcx.erase_and_anonymize_regions(
                                tcx.type_of(field.did).instantiate(tcx, args).skip_normalization(),
                            ));
                        }
                    }
                    // `needs_drop_components` returns an array whole only when its length
                    // is not a known value: it needs drop iff its element does (rustc's
                    // `filter_array_elements`).
                    ty::Array(elem, _) => stack.push(elem),
                    _ => return true,
                }
            }
        }
        false
    }

    /// Inside the freeze, could rustc's own `needs_drop` of `ty` evaluate a constant that may
    /// not be evaluated here ([`non_leaf_constant_if_frozen`])? `false` outside the freeze.
    ///
    /// Trust (fix11, CTFE-IN-MIR-BUILT-1). rustc's query reads an ADT's fields through
    /// `adt_drop_tys`, which NORMALIZES every field type it reaches, and normalizing evaluates
    /// every constant a field names — a field the asked type does not show. MEASURED E0391 on
    /// valid code (stage 1 of `192b4a810f`, `-Ztrust-ir-lower=on` and the default lane; stock
    /// nightly-2026-04-20 accepts it): with `struct W4 { a: [u8; h4()], n: u8 }` and
    /// `const fn h4() -> usize { let w: Option<&W4> = None; match w { Some(r) => r.n as usize,
    /// None => 1 } }`, the producer's drop planner asks `needs_drop(W4)` while `h4`'s MIR is
    /// built (`drops::plan_body`), and rustc's `needs_drop_raw` normalizes `[u8; h4()]`:
    /// "building MIR for `h4`" -> "computing whether `W4` needs drop" -> `h4()`
    /// (`tests/ui/trust/needs_drop_const_field_no_query_cycle.rs`, revision `plain`). The
    /// leak-free walk ([`needs_drop_leak_free`]) asks the same question of each component
    /// before normalizing it.
    ///
    /// The walk visits every type `ty` names and every field of every ADT among them
    /// (`type_of`, unnormalized; a `ManuallyDrop` has none rustc reads), transitively — a
    /// superset of what `needs_drop_raw` normalizes, which stops at a `Copy` component, a
    /// destructor and a `ManuallyDrop`. `true` — the caller's "may need drop" — when any of
    /// them names such a constant, and past its budget.
    #[must_use]
    pub fn needs_drop_may_evaluate_non_leaf_constant<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> bool {
        const MAX_TYPES: usize = 512;
        if !frozen() {
            return false;
        }
        let mut seen: rustc_data_structures::fx::FxHashSet<ty::Ty<'tcx>> = Default::default();
        let mut stack = vec![tcx.erase_and_anonymize_regions(ty)];
        while let Some(ty) = stack.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if seen.len() > MAX_TYPES || non_leaf_constant_if_frozen(tcx, &ty).is_some() {
                return true;
            }
            let _ = walk_types_until(ty, |inner| {
                if let ty::Adt(def, args) = *inner.kind() {
                    if !def.is_manually_drop() {
                        for field in def.all_fields() {
                            stack.push(tcx.erase_and_anonymize_regions(
                                tcx.type_of(field.did).instantiate(tcx, args).skip_normalization(),
                            ));
                        }
                    }
                }
                true
            });
        }
        false
    }

    /// Does `pred` NAME a type a codegen-mode solve would reveal or read the MIR of: an
    /// opaque, a coroutine, a coroutine witness or a coroutine-closure? Free aliases are
    /// expanded first (`type A = Tait;` names `Tait`). Projections are not looked through:
    /// the walk below meets what they normalize to in the obligations their normalization
    /// adds, and an ATPIT value (`type Item = impl Debug`) is an opaque in the normalized
    /// predicate.
    fn names_revealable<'tcx>(tcx: TyCtxt<'tcx>, pred: ty::Predicate<'tcx>) -> bool {
        let pred = if pred.has_type_flags(ty::TypeFlags::HAS_TY_FREE_ALIAS) {
            tcx.expand_free_alias_tys(pred)
        } else {
            pred
        };
        /// A coroutine witness or coroutine-closure anywhere in the visited value: neither
        /// carries a type flag of its own.
        struct CoroutineLike;
        impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for CoroutineLike {
            type Result = std::ops::ControlFlow<()>;
            fn visit_ty(&mut self, t: ty::Ty<'tcx>) -> Self::Result {
                if matches!(t.kind(), ty::CoroutineWitness(..) | ty::CoroutineClosure(..)) {
                    return std::ops::ControlFlow::Break(());
                }
                t.super_visit_with(self)
            }
        }
        pred.has_opaque_types()
            || pred.has_coroutines()
            || pred.visit_with(&mut CoroutineLike).is_break()
    }

    #[derive(Default)]
    struct SessionPrimitiveCopyEnvInert {
        value: Option<bool>,
    }

    thread_local! {
        static PRIMITIVE_COPY_ENV_INERT_CACHE: Cell<Option<(u64, usize, bool)>> =
            const { Cell::new(None) };
    }

    /// A closed primitive `Copy` goal needs no proof-tree observation. The
    /// solver's builtin candidate returns `NoSolution` immediately for scalars
    /// (`instantiate_constituent_tys_for_copy_clone_trait`); core supplies their
    /// real impls. Check those impls without solving and admit only a positive,
    /// non-bound scalar goal in a region-only environment. No ADT, alias,
    /// user-defined trait, structural builtin or opaque premise enters here.
    /// Read the marker declarations too: `no_core` may supply its own lang items.
    pub(super) fn primitive_copy_selection_is_reveal_free<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        predicate: ty::Predicate<'tcx>,
    ) -> bool {
        let Some(ty::PredicateKind::Clause(ty::ClauseKind::Trait(pred))) =
            predicate.kind().no_bound_vars()
        else {
            return false;
        };
        Some(pred.def_id()) == tcx.lang_items().copy_trait()
            && pred.polarity == ty::ClausePolarity::Positive
            && pred.trait_ref.args.len() == 1
            && is_primitive_scalar(pred.self_ty())
            && param_env.caller_bounds().all(|c| {
                matches!(c.kind().skip_binder(), ty::ClauseKind::RegionOutlives(_))
            })
            && primitive_copy_environment_is_inert(tcx)
    }

    fn primitive_copy_environment_is_inert(tcx: TyCtxt<'_>) -> bool {
        let sess_ptr = std::ptr::from_ref(tcx.sess) as usize;
        let epoch_if_frozen = freeze_epoch().filter(|_| frozen());
        if let Some(epoch) = epoch_if_frozen {
            if let Some((cached_epoch, cached_ptr, result)) =
                PRIMITIVE_COPY_ENV_INERT_CACHE.with(Cell::get)
            {
                if cached_epoch == epoch && cached_ptr == sess_ptr {
                    return result;
                }
            }
        }
        let cached = tcx
            .sess
            .with_trust_compiler_state::<SessionPrimitiveCopyEnvInert, _>(|state| state.value);
        let result = cached.unwrap_or_else(|| {
            let computed = primitive_copy_marker_declarations_are_inert(tcx)
                && tcx
                    .lang_items()
                    .copy_trait()
                    .is_some_and(|copy| primitive_trait_impls_inert(tcx, copy))
                && tcx
                    .lang_items()
                    .clone_trait()
                    .is_some_and(|clone| primitive_trait_impls_inert(tcx, clone));
            tcx.sess.with_trust_compiler_state::<SessionPrimitiveCopyEnvInert, _>(|state| {
                state.value = Some(computed);
            });
            computed
        });
        if let Some(epoch) = epoch_if_frozen {
            PRIMITIVE_COPY_ENV_INERT_CACHE.with(|c| c.set(Some((epoch, sess_ptr, result))));
        }
        result
    }

    fn primitive_copy_marker_declarations_are_inert(tcx: TyCtxt<'_>) -> bool {
        let markers = [
            tcx.lang_items().copy_trait(),
            tcx.lang_items().clone_trait(),
            tcx.lang_items().sized_trait(),
            tcx.lang_items().meta_sized_trait(),
            tcx.lang_items().pointee_sized_trait(),
        ];
        markers.iter().all(|&marker| {
            let Some(marker) = marker else { return false };
            let clauses = tcx.clauses_of(marker);
            tcx.generics_of(marker).count() == 1
                && !tcx.trait_is_auto(marker)
                && clauses.parent.is_none()
                && clauses.clauses.iter().all(|&(clause, _)| {
                    let Some(ty::ClauseKind::Trait(pred)) = clause.kind().no_bound_vars() else {
                        return false;
                    };
                    pred.polarity == ty::ClausePolarity::Positive
                        && pred.trait_ref.args.len() == 1
                        && pred.self_ty().is_param(0)
                        && markers.contains(&Some(pred.def_id()))
                })
        })
    }

    /// The next solver discharges nested goals during selection: a `Yes` selection's
    /// returned `ImplSource` deliberately has NO nested obligations. Inspect the solver's
    /// proof tree instead of mistaking that empty list for a reveal-free selection.
    ///
    /// The diagnostic candidate view omits some probes. A bounded strict view must first
    /// account for those: omitted compatibility/shadowing probes, incomplete candidates,
    /// unrepresented assembly goals and rolled-back opaque proposals all decline. Every
    /// remaining candidate is walked in its own probe, including specialization's losing
    /// candidates. Ambiguity, failure, a missing trait candidate or either budget expiring
    /// declines. This is only an admission guard for a later codegen-mode query;
    /// the tree is not proof evidence and never changes a verification grade.
    fn next_selection_is_reveal_free<'tcx>(
        infcx: &rustc_infer::infer::InferCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> bool {
        use std::ops::ControlFlow;

        use rustc_infer::traits::solve::{Certainty, Goal};
        use rustc_trait_selection::solve::inspect::{
            InferCtxtProofTreeExt, InspectConfig, InspectGoal, ProofTreeVisitor,
        };

        const BUDGET: usize = 256;
        struct RevealWalk {
            steps: usize,
        }
        impl<'tcx> ProofTreeVisitor<'tcx> for RevealWalk {
            type Result = ControlFlow<()>;

            fn span(&self) -> rustc_span::Span {
                rustc_span::DUMMY_SP
            }

            fn config(&self) -> InspectConfig {
                InspectConfig { max_depth: BUDGET }
            }

            fn on_recursion_limit(&mut self) -> Self::Result {
                ControlFlow::Break(())
            }

            fn visit_goal(&mut self, goal: &InspectGoal<'_, 'tcx>) -> Self::Result {
                self.steps += 1;
                if self.steps > BUDGET
                    || names_revealable(goal.infcx().tcx, goal.goal().predicate)
                    // Re-evaluating a projected equality can discharge its
                    // normalization before the inspection view represents the
                    // shadowed-environment probe. Decline that missing path.
                    || matches!(
                        goal.goal().predicate.kind().skip_binder(),
                        ty::PredicateKind::Clause(ty::ClauseKind::Projection(_))
                            | ty::PredicateKind::NormalizesTo(_)
                    )
                    || !matches!(goal.result(), Ok(Certainty::Yes))
                {
                    return ControlFlow::Break(());
                }
                if primitive_copy_selection_is_reveal_free(
                    goal.infcx().tcx,
                    goal.goal().param_env,
                    goal.goal().predicate,
                ) {
                    return ControlFlow::Continue(());
                }
                let Some(candidates) = goal.candidates_with_complete_probes(BUDGET) else {
                    return ControlFlow::Break(());
                };
                if candidates.is_empty()
                    && matches!(
                        goal.goal().predicate.kind().skip_binder(),
                        ty::PredicateKind::Clause(ty::ClauseKind::Trait(_))
                    )
                {
                    return ControlFlow::Break(());
                }
                for candidate in candidates {
                    if !matches!(candidate.result(), Ok(Certainty::Yes))
                        || !matches!(candidate.shallow_certainty(), Certainty::Yes)
                    {
                        return ControlFlow::Break(());
                    }
                    // Instantiate and walk higher-ranked goals with the solver's own
                    // universe/constraint handling. Roll each candidate back before the
                    // next one, so one candidate cannot constrain another's arguments.
                    candidate.visit_nested_in_probe(self)?;
                }
                ControlFlow::Continue(())
            }
        }

        infcx
            .visit_proof_tree(
                Goal::new(infcx.tcx, param_env, trait_ref),
                &mut RevealWalk { steps: 0 },
            )
            .is_continue()
    }

    /// A codegen-mode SELECTION of `trait_ref` (`codegen_select_candidate`, the selection
    /// `Instance::try_resolve` and every codegen-mode normalization make), performed instead
    /// in the leak-free mode and WALKED: the selection's nested obligations, the nested
    /// obligations of THEIR selections, and so on, each one required to name nothing
    /// [`names_revealable`] flags and to hold without ambiguity or a proposed hidden type. A
    /// codegen-mode selection of the same trait reference confirms the same impls and meets
    /// the same where-clauses, so it has no opaque of this crate to reveal on that path.
    ///
    /// `None` — the caller's decline — for a trait reference that is itself generic in a way
    /// the empty environment cannot answer, for an ambiguity or error anywhere in the walk,
    /// past the walk's budget, and when any obligation names an opaque or a coroutine (an
    /// opaque reached through an ADT's FIELDS is met as the auto-trait constituent
    /// obligation `Tait: Send`, which names it). Region obligations select nothing and are
    /// skipped; a positive trait obligation, higher-ranked ones included (their bound
    /// variables made placeholders), is selected and walked; an obligation of any other kind
    /// (a projection, `WellFormed`, a const argument) is fulfilled leak-free but not walked
    /// further: a projection's own selection is the trait obligation beside it, which is. A
    /// trait obligation still waiting on an inference variable is retried once another
    /// obligation has made progress.
    ///
    /// The old solver exposes the nested obligations on its `SelectionContext` result. The
    /// next solver discharges those before returning: [`next_selection_is_reveal_free`]
    /// walks its proof tree, including higher-ranked goals and losing candidates.
    ///
    /// Old-solver residual (docs/KNOWN_HAZARDS.md, OPAQUE-IMPL-WHERE-LEAK-1): a selection
    /// between SEVERAL candidates (specialization, an object candidate beside a blanket
    /// impl) evaluates the losing candidates' where-clauses inside the solver, where the
    /// old-solver walk does not see them.
    #[must_use]
    pub fn select_reveal_free<'tcx>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, trait_ref: ty::TraitRef<'tcx>,
    ) -> Option<rustc_middle::traits::ImplSource<'tcx, ()>> {
        select_reveal_free_in_mode(tcx, param_env, trait_ref, true, None)
    }

    // Trust: only the incoming selected-projection fallback uses this narrow
    // policy. Keep its original empty-environment/input/tree guards intact.
    pub(crate) fn select_projection_reveal_free<'tcx>(
        tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>, trait_ref: ty::TraitRef<'tcx>,
    ) -> Option<rustc_middle::traits::ImplSource<'tcx, ()>> {
        select_reveal_free_in_mode(tcx, param_env, trait_ref, false, None)
    }

    fn select_reveal_free_in_mode<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        complete_probes: bool,
        layout_facts: Option<&ClosedLayoutMemo<ty::Ty<'tcx>>>,
    ) -> Option<rustc_middle::traits::ImplSource<'tcx, ()>> {
        use rustc_trait_selection::traits::{
            Obligation, ObligationCause, ObligationCtxt, PredicateObligation, SelectionContext,
        };
        const BUDGET: usize = 256;
        let trait_ref = ty::set_aliases_to_non_rigid(tcx, trait_ref).skip_norm_wip();
        if trait_ref.has_escaping_bound_vars()
            || trait_ref.has_non_region_infer()
            || param_env.has_infer()
            || names_revealable(tcx, trait_ref.upcast(tcx))
        {
            return None;
        }
        let empty_caller_bounds = param_env.is_empty();
        let mode = if complete_probes {
            leak_free_typing_mode(tcx)
        } else {
            ty::TypingMode::OpaqueAnalysis
        };
        let (infcx, param_env) = leak_free_infcx(tcx, param_env, mode);
        let selected = (|| {
            // The next solver discharges nested goals while constructing the tree, before
            // the visitor can refuse them. Never begin that eager solve inside the freeze
            // when an impl header, where-clause or caller-bound path could evaluate CTFE.
            if infcx.next_trait_solver()
                && frozen()
                && !next_selection_is_const_inert(tcx, param_env, trait_ref)
            {
                return None;
            }
            if infcx.next_trait_solver() {
                // The new selected-projection fallback owns the incoming narrow
                // OpaqueAnalysis policy. Existing codegen selection owns the complete
                // probe policy; do not silently substitute one after the other refuses.
                if !complete_probes {
                    if !empty_caller_bounds {
                        return None;
                    }
                    return match layout_facts {
                        Some(facts) => next_solver_reveal_free::select_with_layout_facts(
                            &infcx, param_env, trait_ref, facts,
                        ),
                        None => next_solver_reveal_free::select(&infcx, param_env, trait_ref),
                    };
                }
            }
            let mut selcx = SelectionContext::new(&infcx);
            // Obligations of every kind but a trait one are decided by the solver itself, in
            // fulfillment, so that one may constrain an inference variable a deferred trait
            // obligation waits on (`I: Iterator<Item = T>` binds `T` for `T: Sized`).
            let ocx = ObligationCtxt::new(&infcx);
            let root: rustc_infer::traits::TraitObligation<'tcx> = Obligation::new(
                tcx,
                ObligationCause::dummy(),
                param_env,
                with_region_vars(&infcx, trait_ref),
            );
            if infcx.next_trait_solver() {
                if !next_selection_is_reveal_free(&infcx, param_env, root.predicate.trait_ref)
                {
                    return None;
                }
                return selcx.select(&root).ok().flatten().map(|source| source.map(|_| ()));
            }
            let source = match selcx.select(&root) {
                Ok(Some(source)) => source,
                Ok(None) | Err(_) => return None,
            };
            let mut work: Vec<PredicateObligation<'tcx>> =
                source.borrow_nested_obligations().to_vec();
            let mut deferred: Vec<PredicateObligation<'tcx>> = Vec::new();
            let mut steps = 0usize;
            loop {
                let mut progressed = false;
                while let Some(obligation) = work.pop() {
                    steps += 1;
                    if steps > BUDGET {
                        return None;
                    }
                    let predicate = infcx.deeply_resolve_via_unification_table(obligation.predicate);
                    if names_revealable(tcx, predicate) {
                        return None;
                    }
                    let kind = predicate.kind();
                    match kind.skip_binder() {
                        ty::PredicateKind::Clause(
                            ty::ClauseKind::RegionOutlives(..) | ty::ClauseKind::TypeOutlives(..),
                        ) => {}
                        ty::PredicateKind::Clause(ty::ClauseKind::Trait(trait_pred))
                            if trait_pred.polarity == ty::ClausePolarity::Positive =>
                        {
                            // A HIGHER-RANKED trait obligation is walked too (its bound
                            // variables made placeholders, as the solver's own `match_impl`
                            // makes them, so the same impl is selected). Handed to fulfillment
                            // instead, `for<'a> &'a X: Tr2` was PROVED leak-free without its
                            // impl's where-clauses being looked at — `impl<'a> Tr2 for &'a X
                            // where Tait: Debug` holds there from `Tait`'s own bound — while
                            // the codegen-mode selection normalizes `Tait: Debug` and reveals
                            // `Tait`: E0391 inside `mir_built` of `Tait`'s defining body on
                            // valid Rust (`impl_where_leak_higher_ranked.rs`).
                            let trait_pred =
                                infcx.enter_forall_and_leak_universe(kind.rebind(trait_pred));
                            let nested = obligation.with(tcx, trait_pred);
                            match selcx.select(&nested) {
                                Ok(Some(source)) => {
                                    progressed = true;
                                    work.extend(source.nested_obligations());
                                }
                                Ok(None) if predicate.has_non_region_infer() => {
                                    deferred.push(obligation);
                                }
                                Ok(None) | Err(_) => return None,
                            }
                        }
                        _ => {
                            ocx.register_obligation(obligation.with(tcx, predicate));
                            if !ocx.try_evaluate_obligations().no_errors() {
                                return None;
                            }
                            progressed = true;
                        }
                    }
                }
                if deferred.is_empty() {
                    break;
                }
                if !progressed {
                    return None;
                }
                work.append(&mut deferred);
            }
            if !ocx.evaluate_obligations_error_on_ambiguity().no_errors() {
                return None;
            }
            Some(source.map(|_| ()))
        })();
        let defined = proposed_hidden_type(&infcx);
        let selected = infcx.deeply_resolve_via_unification_table(selected.filter(|_| !defined)?);
        if selected.has_non_region_infer() {
            return None;
        }
        Some(tcx.erase_and_anonymize_regions(selected))
    }

    mod next_solver_reveal_free;

    /// Exercise the real proof-tree walk's exhaustion paths in compiler-backed tests.
    #[cfg(test)]
    pub(crate) fn next_solver_selection_with_limits_for_test<'tcx>(
        tcx: TyCtxt<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        max_work: usize,
        max_depth: usize,
    ) -> bool {
        let trait_ref = ty::set_aliases_to_non_rigid(tcx, trait_ref).skip_norm_wip();
        let (infcx, param_env) = leak_free_infcx(tcx, ty::ParamEnv::empty(), ty::TypingMode::OpaqueAnalysis);
        assert!(infcx.next_trait_solver());
        let selected = next_solver_reveal_free::select_with_limits(
            &infcx, param_env, trait_ref, max_work, max_depth,
        );
        let defined = proposed_hidden_type(&infcx);
        selected.is_some() && !defined
    }

    /// May a codegen-mode `Instance::try_resolve` / `Instance::resolve_for_fn_ptr` of
    /// `def_id` at `args` be asked right now? Outside the leak-free requirement
    /// ([`leak_free_required`]), and for an item no trait owns, yes: the caller's own guards
    /// stand. A trait item is resolved by SELECTING its trait reference, whose impls'
    /// where-clauses a codegen-mode selection reveals: admitted only when
    /// [`select_reveal_free`] walks that selection.
    #[must_use]
    pub fn resolution_reveal_free<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        def_id: rustc_span::def_id::DefId,
        args: ty::GenericArgs<'tcx>,
    ) -> bool {
        if !leak_free_required(tcx) {
            return true;
        }
        let Some(trait_def_id) = tcx.trait_of_assoc(def_id) else {
            return true;
        };
        let trait_ref = ty::TraitRef::from_assoc(tcx, trait_def_id, args);
        select_reveal_free(tcx, param_env, trait_ref).is_some()
    }

    /// Visit every DISTINCT `Ty<'tcx>` reachable through `ty` using the same traversal
    /// rules as `ty.walk().filter_map(|arg| arg.as_type())`, without allocating
    /// `TypeWalker`'s `SmallVec` stack. Returns `false` as soon as `f` returns `false`.
    ///
    /// Each distinct type is visited once, exactly as `TypeWalker`'s visited table
    /// does. Trust (2026-11-07): the first cut of this helper (3607f0f8997) dropped the
    /// visited table, which made the walk exponential in the depth of a type whose
    /// subterms are shared: `PolyBox<(T, T)>`'s polymorphic-recursion field tree in
    /// `needs_drop_may_evaluate_non_leaf_constant` ran for more than 45 CPU minutes
    /// (`tests/ui/trust/assume_total_does_not_cover_callee_requires.rs`
    /// `recursive_type_certify`). `SsoHashSet` keeps small walks allocation-free.
    #[inline]
    pub(crate) fn walk_types_until<'tcx>(
        ty: ty::Ty<'tcx>,
        mut f: impl FnMut(ty::Ty<'tcx>) -> bool,
    ) -> bool {
        use rustc_data_structures::sso::SsoHashSet;
        use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
        use std::ops::ControlFlow;

        struct WalkTypesVisitor<'tcx, F> {
            f: F,
            visited: SsoHashSet<ty::Ty<'tcx>>,
        }
        impl<'tcx, F: FnMut(ty::Ty<'tcx>) -> bool> TypeVisitor<TyCtxt<'tcx>>
            for WalkTypesVisitor<'tcx, F>
        {
            type Result = ControlFlow<()>;

            #[inline]
            fn visit_ty(&mut self, t: ty::Ty<'tcx>) -> Self::Result {
                if !self.visited.insert(t) {
                    return ControlFlow::Continue(());
                }
                if !(self.f)(t) {
                    return ControlFlow::Break(());
                }
                t.super_visit_with(self)
            }

            #[inline]
            fn visit_const(&mut self, c: ty::Const<'tcx>) -> Self::Result {
                match c.kind() {
                    ty::ConstKind::Value(cv) => cv.ty.visit_with(self),
                    ty::ConstKind::Expr(expr) => expr.args().visit_with(self),
                    ty::ConstKind::Alias(_, ct) => ct.args.visit_with(self),
                    ty::ConstKind::Infer(_)
                    | ty::ConstKind::Param(_)
                    | ty::ConstKind::Placeholder(_)
                    | ty::ConstKind::Bound(..)
                    | ty::ConstKind::Error(_) => ControlFlow::Continue(()),
                }
            }
        }

        ty.visit_with(&mut WalkTypesVisitor { f: &mut f, visited: SsoHashSet::new() })
            .is_continue()
    }

    /// The type's OWN flags admit a codegen-mode query: nothing generic, inferred,
    /// placeholder, aliased, coroutine, coroutine witness, or carrying escaping bound
    /// variables. Not sufficient on its own — see
    /// [`layout_query_is_reentrant_safe_deep`].
    #[must_use]
    pub fn layout_query_is_reentrant_safe<'tcx>(ty: ty::Ty<'tcx>) -> bool {
        const FORBIDDEN_FLAGS: ty::TypeFlags = ty::TypeFlags::from_bits_retain(
            (ty::TypeFlags::HAS_PARAM.bits() & !ty::TypeFlags::HAS_RE_PARAM.bits())
                | (ty::TypeFlags::HAS_INFER.bits() & !ty::TypeFlags::HAS_RE_INFER.bits())
                | (ty::TypeFlags::HAS_PLACEHOLDER.bits()
                    & !ty::TypeFlags::HAS_RE_PLACEHOLDER.bits())
                | ty::TypeFlags::HAS_ALIAS.bits()
                | ty::TypeFlags::HAS_TY_CORO.bits(),
        );
        !ty.has_type_flags(FORBIDDEN_FLAGS)
            && !ty.has_escaping_bound_vars()
            && walk_types_until(ty, |inner| !matches!(inner.kind(), ty::CoroutineWitness(..)))
    }

    // ---- L2: WHICH UNEVALUATED CONSTANTS A TYPE QUERY MAY EVALUATE FROM INSIDE `mir_built` ----
    //
    // Trust (fix11, L2). A field type that names an unevaluated constant (`[u8; N]`,
    // `pattern_type!(u32 is 1..)`'s range end, the anonymous constant `RangePattern::MAX` at
    // `u32`) carries the alias flag, so the funnel used to decline every struct reaching one —
    // in `core`, every `NonZero<uN>` (through `niche_types::*Inner`) and `DecimalSeq`.
    // `layout_of` evaluates the constant, and evaluating it is CTFE: `eval_to_valtree` ->
    // `mir_for_ctfe` -> `mir_borrowck` -> `mir_built` of every body the evaluation runs. From
    // inside `mir_built` that is an E0391 hard error exactly when one of those queries is
    // already on this thread's query stack (measured: `tests/ui/trust/
    // leaf_const_field_ctfe_no_query_cycle.rs`, through the MIR oracle's array lengths).
    //
    // The class admitted here is the one for which that cannot happen, decided from what the
    // evaluation WILL RUN, not from where we are: a constant whose whole CTFE closure K is LEAF
    // bodies. A leaf body is a const / associated const / anonymous const of primitive scalar
    // type whose HIR is built only from literals, unary `-`/`!`, binary operators, casts,
    // statement-free blocks, paths to further constants and the layout queries
    // `size_of::<P>()` / `align_of::<P>()` over a primitive scalar or unit `P` or a pointer or
    // reference to one ([`layout_call_target`]), every one of whose (sub)expressions has a
    // primitive scalar type and no adjustment. The layout queries' own bodies (`size_of`,
    // `align_of`, `SizedTypeProperties::SIZE`/`ALIGN` through its one blanket impl, and the
    // intrinsic) are fixed `core` items that read `layout_of(P)` and nothing else, and are
    // bodies of the closure like any leaf body ([`may_be_leaf_body`]). A TRAIT associated
    // constant is followed to the item of the ONE impl that can apply ([`sole_impl_item`],
    // read without asking selection). A FOREIGN constant whose arguments name no local def is a
    // leaf too: its CTFE runs metadata MIR and dispatches only on its arguments (the existing
    // `frozen_ctfe_may_reach_local_body` safe class).
    //
    // INERT below means: an item query over HIR or an impl header (`type_of` of a non-opaque
    // item, `generics_of`, `predicates_of`, `impl_trait_header`, `trait_impls_of`,
    // `inherent_impls`, `associated_items`), or a trait selection / path probe all of whose
    // candidates have alias-free headers and only alias-free outlives and `Sized`-family
    // where-clauses whose struct-tail chain names no alias either ([`clause_is_inert`]) — it
    // evaluates no constant and builds no body. Why evaluating K is cycle-free:
    //
    //   * every query a K body's evaluation demands is a K-query (`typeck`, `thir_body`,
    //     `mir_built`, `mir_borrowck`, `mir_for_ctfe` or the evaluation of a body in K) or
    //     inert. `typeck` of a K body is inert because everything it can select or probe is
    //     checked INERT FROM HIR BEFORE `typeck` IS ASKED ([`leaf_shape`]): the body's own
    //     where-clauses, those of every item a path names, every impl of the trait a
    //     trait-constant path names, every candidate the probe of a `Type::NAME` path can
    //     consider (the self type's inherent impls with an item of that name, and every
    //     in-scope trait with one), and every impl of each operator's trait whose self type is
    //     a primitive scalar or a parameter. CTFE of a trait constant selects the one inert impl
    //     and resolves its item through the trait's specialization graph, whose overlap checks
    //     run over impls that are all inert;
    //   * so a cycle needs a K-query ALREADY on this thread's stack. Take the topmost one:
    //     every frame above it was demanded while processing it, so by the first point each is
    //     a K-query or inert, and an inert query enters no `mir_built`. The `mir_built` this
    //     funnel runs inside is then itself a K-query, `mir_built(k)` of a leaf body `k`, whose
    //     hook holds a freeze frame naming `k`. That case is DECLINED directly
    //     ([`evaluation_admitted_here`]): nothing is evaluated while any freeze frame on this
    //     thread names a body some leaf closure could contain ([`may_be_leaf_body`]: a
    //     primitive-typed, leaf-shaped constant, or a layout query's body) or names no body at
    //     all. It does not rest on the claim that a leaf body's hook never asks a struct's
    //     layout;
    //   * the decision itself asks HIR, inert item queries, and `typeck` of a leaf-SHAPED body
    //     only after its shape and every candidate above passed.
    //
    // What the argument does NOT cover, recorded in docs/KNOWN_HAZARDS.md (L2-LEAF-CTFE-1): a
    // Trust hook that runs inside a K-query OUTSIDE any freeze (the `mir_for_ctfe` flip seam)
    // and demands a query keyed on another body — `mir_built`'s effect census runs under a
    // freeze frame naming its body (OPAQUE-IMPL-WHERE-LEAK-1 (5)), so its evaluations pass
    // [`evaluation_admitted_here`], though a non-CTFE demand it made keyed on another body
    // would still reopen the argument; the foreign class's dispatch argument; and the parallel
    // front end, where a K-query held by another thread is waited on rather than detected on
    // this one. (A `Sized` obligation over a
    // concrete type reads its struct tail; a tail chain that names an alias is no longer inert:
    // [`sizedness_proof_reads_no_alias`].)
    //
    // NOT admitted, fail-closed: any other call (a `const fn`; a signed niche's exclusive end
    // `RangePattern::sub_one(0)`; `size_of` over an ADT, a parameter or a slice), any generic
    // parameter or non-primitive argument, an inline
    // const, a static, a const parameter, a block with statements, a non-primitive
    // (sub)expression type, an inferred (`_`) declared type, a where-clause on the constant,
    // its impl or its trait that is not inert, a trait constant whose trait has a non-inert
    // impl or more than one candidate impl, a blanket impl, a generic or where-claused impl or
    // an item the impl does not itself define, a `Type::NAME` path whose probe could consider a
    // non-inert candidate, an operator whose trait has a non-inert impl over a primitive or
    // parameter self type, a closure deeper than [`LEAF_MAX_DEFS`] constants or
    // [`LEAF_MAX_EXPRS`] expressions, any constant the evaluation does not resolve to a value,
    // and every constant while a freeze frame on this thread lowers a body a leaf closure could
    // contain or names no body. The constant is then left unevaluated and the caller's own-flags check
    // declines it exactly as before.

    /// At most this many distinct constants in one leaf closure.
    const LEAF_MAX_DEFS: usize = 32;
    /// At most this many HIR expressions walked over one leaf closure.
    const LEAF_MAX_EXPRS: usize = 512;

    fn is_primitive_scalar(t: ty::Ty<'_>) -> bool {
        matches!(t.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_))
    }

    // Query-inert typing only, not constant evaluation or validity authority.
    fn exact_primitive_const_type<'tcx>(constant: ty::Const<'tcx>, expected: ty::Ty<'tcx>) -> bool {
        is_primitive_scalar(expected)
            && matches!(constant.kind(), ty::ConstKind::Value(value) if value.ty == expected)
    }

    #[cfg(test)]
    pub(super) fn assert_concrete_const_typing_controls<'tcx>(
        tcx: TyCtxt<'tcx>, deferred: ty::Const<'tcx>,
    ) {
        use ty::Upcast;
        let value = ty::Const::from_bits(
            tcx, 2, ty::TypingEnv::fully_monomorphized(), tcx.types.usize,
        );
        let param = ty::Const::new_param(tcx, ty::ParamConst {
            index: 0, name: rustc_span::Symbol::intern("N"),
        });
        let bound = ty::Const::new_anon_bound(tcx, ty::INNERMOST, ty::BoundVar::from_u32(0));
        assert!(exact_primitive_const_type(value, tcx.types.usize));
        assert!(!exact_primitive_const_type(value, tcx.types.u32));
        assert!(!exact_primitive_const_type(value, tcx.types.unit));
        assert!(!exact_primitive_const_type(param, tcx.types.usize));
        assert!(!exact_primitive_const_type(bound, tcx.types.usize));
        assert!(!matches!(deferred.kind(), ty::ConstKind::Value(_)));
        assert!(!exact_primitive_const_type(deferred, tcx.types.usize));
        for (constant, expected, admit) in [
            (value, tcx.types.usize, true),
            (value, tcx.types.u32, false),
            (value, tcx.types.unit, false),
            (param, tcx.types.usize, false),
            (deferred, tcx.types.usize, false),
        ] {
            let clause: ty::Clause<'tcx> =
                ty::ClauseKind::ConstArgHasType(constant, expected).upcast(tcx);
            assert_eq!(clause_is_inert(tcx, clause, None), admit);
        }
        let variables = tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Const]);
        for constant in [value, bound] {
            let clause: ty::Clause<'tcx> = ty::Binder::bind_with_vars(
                ty::ClauseKind::ConstArgHasType(constant, tcx.types.usize), variables,
            ).upcast(tcx);
            assert!(!clause_is_inert(tcx, clause, None));
        }
    }

    /// Every argument is a primitive scalar type or a region.
    fn args_are_primitive(args: ty::GenericArgs<'_>) -> bool {
        args.iter().all(|a| match a.kind() {
            ty::GenericArgKind::Lifetime(_) => true,
            ty::GenericArgKind::Type(t) => is_primitive_scalar(t),
            ty::GenericArgKind::Const(_) => false,
        })
    }

    /// Which impls of a trait a selection can consider.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum CandidateScope {
        /// Every impl: a trait constant (its CTFE resolves the item through the trait's
        /// specialization graph, built over every impl) or an in-scope trait a path probe can
        /// consider.
        Every,
        /// The blanket impls and the impls whose self type is a primitive scalar: the
        /// operator traits over primitive scalar operands. Selection rejects every other impl
        /// by its self type before confirming anything (`DeepRejectCtxt`).
        PrimitiveSelf,
    }

    struct LeafWalk<'tcx> {
        proven: Vec<(DefId, ty::GenericArgs<'tcx>)>,
        in_progress: Vec<DefId>,
        /// Traits already answered by [`trait_selection_inert`] in this walk.
        traits: Vec<(DefId, CandidateScope, bool)>,
        defs: usize,
        exprs: usize,
    }

    /// The item a const alias names. Upstream 1.101 removed
    /// `AliasConstKind::opt_def_id`; every kind names a `DefId` now.
    pub(crate) fn alias_const_def_id(kind: ty::AliasConstKind) -> Option<DefId> {
        use ty::AliasConstKind;
        Some(match kind {
            AliasConstKind::Projection { def_id }
            | AliasConstKind::InherentSelf { def_id }
            | AliasConstKind::InherentImpl { def_id }
            | AliasConstKind::Free { def_id }
            | AliasConstKind::Anon { def_id } => def_id,
        })
    }

    /// May the constant `def` at `args` be evaluated on this thread right now: is its whole
    /// CTFE closure leaf ([`ctfe_closure_is_leaf`]), and does no freeze frame on this thread
    /// forbid it ([`evaluation_admitted_here`])? `false` is the fail-closed answer. Every site
    /// that evaluates a constant inside the freeze asks this.
    #[must_use]
    pub fn may_evaluate_constant<'tcx>(
        tcx: TyCtxt<'tcx>,
        def: DefId,
        args: ty::GenericArgs<'tcx>,
    ) -> bool {
        evaluation_admitted_here(tcx) && ctfe_closure_is_leaf(tcx, def, args)
    }

    /// Is the CTFE closure of the constant `def` at `args` made only of leaf bodies (see the
    /// L2 note above)? `false` is the fail-closed answer. Where the closure is evaluated is
    /// not asked here: see [`may_evaluate_constant`].
    #[must_use]
    pub fn ctfe_closure_is_leaf<'tcx>(
        tcx: TyCtxt<'tcx>,
        def: DefId,
        args: ty::GenericArgs<'tcx>,
    ) -> bool {
        let mut walk = LeafWalk {
            proven: Vec::new(),
            in_progress: Vec::new(),
            traits: Vec::new(),
            defs: 0,
            exprs: 0,
        };
        leaf_const(tcx, def, args, &mut walk)
    }

    fn leaf_const<'tcx>(
        tcx: TyCtxt<'tcx>,
        def: DefId,
        args: ty::GenericArgs<'tcx>,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_hir::def::DefKind;
        if args.has_non_region_param()
            || args.has_non_region_infer()
            || args.has_non_region_placeholders()
            || args.has_escaping_bound_vars()
            || args.has_aliases()
            || args.references_error()
        {
            return false;
        }
        // A FOREIGN constant whose arguments name no local def: its CTFE runs metadata MIR
        // and cannot demand a query keyed on this crate (`frozen_ctfe_may_reach_local_body`).
        if !def.is_local() {
            return matches!(
                tcx.def_kind(def),
                DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::AnonConst
            ) && !args.iter().any(crate::convert::generic_arg_mentions_local_def);
        }
        if !args_are_primitive(args) {
            return false;
        }
        if walk.proven.iter().any(|&(d, k)| d == def && k == args) {
            return true;
        }
        if walk.in_progress.contains(&def) {
            return false;
        }
        walk.defs += 1;
        if walk.defs > LEAF_MAX_DEFS {
            return false;
        }
        let kind = tcx.def_kind(def);
        // A TRAIT associated constant runs the item of the one impl that can apply.
        if matches!(kind, DefKind::AssocConst { .. })
            && matches!(tcx.def_kind(tcx.parent(def)), DefKind::Trait)
        {
            let Some(item) = sole_impl_item(tcx, def, args, walk) else { return false };
            walk.in_progress.push(def);
            let ok = leaf_const(tcx, item, ty::GenericArgs::empty(), walk);
            walk.in_progress.pop();
            if ok {
                walk.proven.push((def, args));
            }
            return ok;
        }
        if !matches!(kind, DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::AnonConst)
        {
            return false;
        }
        let Some(local) = def.as_local() else { return false };
        let Some(body) = tcx.hir_maybe_body_owned_by(local) else { return false };
        // An inferred declared type (`const C: _`) is computed by `typeck` itself.
        if tcx
            .hir_node_by_def_id(local)
            .ty()
            .is_some_and(|t| matches!(t.kind, rustc_hir::TyKind::Infer(..)))
        {
            return false;
        }
        // Shape first, from HIR and inert item queries alone: only then is `typeck` asked.
        if !item_predicates_inert(tcx, def, None) || !leaf_shape(tcx, &body.value, walk) {
            return false;
        }
        let declared = tcx.type_of(def).instantiate(tcx, args).skip_normalization();
        if !is_primitive_scalar(declared) {
            return false;
        }
        let typeck = tcx.typeck(local);
        if typeck.tainted_by_errors.is_some() {
            return false;
        }
        walk.in_progress.push(def);
        let ok = leaf_expr(tcx, typeck, &body.value, args, walk);
        walk.in_progress.pop();
        if ok {
            walk.proven.push((def, args));
        }
        ok
    }

    /// The item a codegen-mode resolution of the LOCAL trait constant `def` at `args` runs —
    /// read WITHOUT asking selection, and only when selection has exactly one candidate that
    /// it confirms without evaluating anything: the constant's and the trait's where-clauses
    /// are inert, every impl of the trait is inert ([`trait_selection_inert`], which also
    /// keeps auto and lang-item traits out: those have built-in candidates), the trait has no
    /// blanket impl and exactly one impl for the self type's simplified form; that impl is
    /// non-generic, has no predicates, is not `default`, is a positive impl of exactly `args`,
    /// and itself defines `def` (no specialization parent or trait default is consulted).
    /// `None` is the fail-closed answer. Everything read here is an item query over HIR or an
    /// impl header.
    fn sole_impl_item<'tcx>(
        tcx: TyCtxt<'tcx>,
        def: DefId,
        args: ty::GenericArgs<'tcx>,
        walk: &mut LeafWalk<'tcx>,
    ) -> Option<DefId> {
        use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
        let trait_def_id = tcx.parent(def);
        if args.len() != tcx.generics_of(trait_def_id).count()
            || tcx.generics_of(def).count() != args.len()
            || !args.iter().all(|a| a.as_type().is_some_and(is_primitive_scalar))
            || !item_predicates_inert(tcx, def, Some(trait_def_id))
            || !trait_selection_inert(tcx, trait_def_id, CandidateScope::Every, walk)
        {
            return None;
        }
        let simplified = simplify_type(tcx, args.type_at(0), TreatParams::AsRigid)?;
        let impls = tcx.trait_impls_of(trait_def_id);
        if !impls.blanket_impls().is_empty() {
            return None;
        }
        let &[impl_def_id] = impls.non_blanket_impls().get(&simplified)?.as_slice() else {
            return None;
        };
        if tcx.generics_of(impl_def_id).count() != 0
            || !tcx.clauses_of(impl_def_id).clauses.is_empty()
            || tcx.defaultness(impl_def_id).is_default()
        {
            return None;
        }
        let header = tcx.impl_trait_header(impl_def_id);
        if header.polarity != ty::ImplPolarity::Positive
            || header.trait_ref.instantiate_identity().skip_norm_wip().args != args
        {
            return None;
        }
        let item = *tcx.impl_item_implementor_ids(impl_def_id).get(&def)?;
        if tcx.defaultness(item).is_default() || tcx.generics_of(item).count() != 0 {
            return None;
        }
        Some(item)
    }

    /// The leaf GRAMMAR, read from HIR and inert item queries only — the gate `typeck` of the
    /// body is asked behind. Every HIR type the body spells (a cast target, a path's qualified
    /// self) must be [`benign_hir_ty`] and no path segment may carry generic arguments
    /// (`typeck` registers well-formedness for those types, and a type naming a constant would
    /// start its CTFE from inside `typeck`); and everything `typeck` can select or probe for
    /// the body's paths and operators must be inert (the L2 note above).
    fn leaf_shape<'tcx>(
        tcx: TyCtxt<'tcx>,
        e: &rustc_hir::Expr<'_>,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_hir::def::{DefKind, Res};
        use rustc_hir::{BlockCheckMode, ExprKind, QPath, UnOp};
        walk.exprs += 1;
        if walk.exprs > LEAF_MAX_EXPRS {
            return false;
        }
        match e.kind {
            ExprKind::Lit(_) => true,
            ExprKind::Path(QPath::Resolved(qself, path)) => {
                path.segments.iter().all(|seg| seg.args.is_none())
                    && qself.is_none_or(|t| benign_hir_ty(tcx, t).is_some())
                    && match path.res {
                        Res::Def(DefKind::Const { .. }, did) => item_predicates_inert(tcx, did, None),
                        Res::Def(DefKind::AssocConst { .. }, did) => {
                            assoc_const_path_inert(tcx, did, walk)
                        }
                        _ => false,
                    }
            }
            ExprKind::Path(QPath::TypeRelative(qself, seg)) => {
                seg.args.is_none()
                    && benign_hir_ty(tcx, qself).is_some_and(|self_ty| {
                        type_relative_probe_inert(tcx, e.hir_id, self_ty, seg.ident.name, walk)
                    })
            }
            ExprKind::Cast(inner, target) => {
                benign_hir_ty(tcx, target).is_some() && leaf_shape(tcx, inner, walk)
            }
            ExprKind::Call(callee, []) => layout_call_target(tcx, callee)
                .is_some_and(|did| item_predicates_inert(tcx, did, None)),
            ExprKind::Unary(op @ (UnOp::Neg | UnOp::Not), inner) => {
                let item = match op {
                    UnOp::Neg => rustc_attr_ir::lang_items::LangItem::Neg,
                    _ => rustc_attr_ir::lang_items::LangItem::Not,
                };
                operator_selection_inert(tcx, Some(item), walk) && leaf_shape(tcx, inner, walk)
            }
            ExprKind::DropTemps(inner) => leaf_shape(tcx, inner, walk),
            ExprKind::Binary(op, l, r) => {
                operator_selection_inert(tcx, binop_lang_item(op.node), walk)
                    && leaf_shape(tcx, l, walk)
                    && leaf_shape(tcx, r, walk)
            }
            ExprKind::Block(block, None) => {
                block.stmts.is_empty()
                    && matches!(block.rules, BlockCheckMode::DefaultBlock)
                    && !block.targeted_by_break
                    && block.expr.is_some_and(|tail| leaf_shape(tcx, tail, walk))
            }
            _ => false,
        }
    }

    /// The trait `typeck` selects for a binary operator (`None` for `&&` and `||`, which are
    /// built in over `bool` and select nothing).
    fn binop_lang_item(op: rustc_hir::BinOpKind) -> Option<rustc_attr_ir::lang_items::LangItem> {
        use rustc_attr_ir::lang_items::LangItem as L;
        use rustc_hir::BinOpKind as B;
        Some(match op {
            B::Add => L::Add,
            B::Sub => L::Sub,
            B::Mul => L::Mul,
            B::Div => L::Div,
            B::Rem => L::Rem,
            B::BitXor => L::BitXor,
            B::BitAnd => L::BitAnd,
            B::BitOr => L::BitOr,
            B::Shl => L::Shl,
            B::Shr => L::Shr,
            B::Eq | B::Ne => L::PartialEq,
            B::Lt | B::Le | B::Gt | B::Ge => L::PartialOrd,
            B::And | B::Or => return None,
        })
    }

    /// Is `did` `core::mem::size_of` or `core::mem::align_of`?
    fn is_layout_query_fn(tcx: TyCtxt<'_>, did: DefId) -> bool {
        tcx.get_diagnostic_name(did)
            .is_some_and(|name| matches!(name.as_str(), "mem_size_of" | "mem_align_of"))
    }

    /// The one call a leaf body may make, read from HIR: `size_of::<P>()` or `align_of::<P>()`
    /// (`core::mem`'s, by diagnostic item) spelled as a plain path with one written type
    /// argument `P` that is a primitive scalar, `()`, or a raw pointer or reference to one, and
    /// no other generic argument anywhere in the path. Its CTFE reads `layout_of(P)` through
    /// `core`'s own `size_of`/`align_of` body, `SizedTypeProperties::SIZE`/`ALIGN` (the trait's
    /// one blanket impl) and the intrinsic: no body of the program, nothing a type reaches.
    /// `TypeId`'s `16 / size_of::<*const ()>()` is this shape. Returns the callee.
    fn layout_call_target(tcx: TyCtxt<'_>, callee: &rustc_hir::Expr<'_>) -> Option<DefId> {
        use rustc_hir::def::{DefKind, Res};
        use rustc_hir::{ExprKind, GenericArg, QPath, TyKind};
        let ExprKind::Path(QPath::Resolved(None, path)) = callee.kind else { return None };
        let Res::Def(DefKind::Fn, did) = path.res else { return None };
        if !is_layout_query_fn(tcx, did) {
            return None;
        }
        let (last, rest) = path.segments.split_last()?;
        if rest.iter().any(|seg| seg.args.is_some()) {
            return None;
        }
        let args = last.args?;
        let [GenericArg::Type(arg)] = args.args else { return None };
        if !args.constraints.is_empty() {
            return None;
        }
        let leaf = |t: &rustc_hir::Ty<'_>| {
            matches!(t.kind, TyKind::Tup([]))
                || benign_hir_ty(tcx, t).is_some_and(is_primitive_scalar)
        };
        let arg = arg.as_unambig_ty();
        let ok = match arg.kind {
            TyKind::Ptr(pointee, _) | TyKind::Ref(_, pointee, _) => leaf(pointee),
            _ => leaf(arg),
        };
        ok.then_some(did)
    }

    /// The type argument of an admitted layout call, as `typeck` resolved it: a primitive
    /// scalar or `()`, or a raw pointer or reference to one.
    fn layout_primitive_ty(t: ty::Ty<'_>) -> bool {
        let leaf = |p: ty::Ty<'_>| is_primitive_scalar(p) || p.is_unit();
        match t.kind() {
            ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _) => leaf(*pointee),
            _ => leaf(t),
        }
    }

    /// `typeck` of an operator over primitive scalar operands selects the operator's trait
    /// with a primitive (or integer/float inference variable) self type: every impl it can
    /// consider is inert. `item` is `None` for an operator that selects nothing.
    fn operator_selection_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        item: Option<rustc_attr_ir::lang_items::LangItem>,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        let Some(item) = item else { return true };
        // No such lang item: `typeck` cannot select an overloaded operator at all.
        let Some(trait_def_id) = tcx.lang_items().get(item) else { return true };
        trait_selection_inert(tcx, trait_def_id, CandidateScope::PrimitiveSelf, walk)
    }

    /// A path `<Q as Trait>::C`, `Trait::C` or (inherent) `C` resolved by name to the
    /// associated constant `did`: `typeck` registers its predicates (with its parent's) and,
    /// for a trait constant, selects the trait over the constant's self type.
    fn assoc_const_path_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        did: DefId,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_hir::def::DefKind;
        let parent = tcx.parent(did);
        match tcx.def_kind(parent) {
            DefKind::Trait => {
                item_predicates_inert(tcx, did, Some(parent))
                    && trait_selection_inert(tcx, parent, CandidateScope::Every, walk)
            }
            DefKind::Impl { of_trait: false } => {
                inherent_impl_inert(tcx, parent) && item_predicates_inert(tcx, did, None)
            }
            _ => false,
        }
    }

    /// `typeck` of the path `<self_ty>::name` (or `SelfTy::name`) probes the self type's
    /// inherent impls, then the traits in scope at the path, for an item called `name`, and
    /// checks the where-clauses of each candidate it considers. Every one of them is inert:
    /// each inherent impl of the self type (and each incoherent impl of its simplified form)
    /// with an item of that name, and every in-scope trait with one.
    fn type_relative_probe_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        scope: rustc_hir::HirId,
        self_ty: ty::Ty<'tcx>,
        name: rustc_span::Symbol,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
        let Some(simplified) = simplify_type(tcx, self_ty, TreatParams::InstantiateWithInfer)
        else {
            return false;
        };
        let names = |container: DefId| {
            tcx.associated_items(container).filter_by_name_unhygienic(name).next().is_some()
        };
        let adt_impls: &[DefId] = match self_ty.kind() {
            ty::Adt(adt, _) => tcx.inherent_impls(adt.did()),
            _ => &[],
        };
        adt_impls
            .iter()
            .chain(tcx.incoherent_impls(simplified))
            .filter(|&&i| names(i))
            .all(|&i| inherent_impl_inert(tcx, i))
            && tcx
                .in_scope_traits(scope)
                .into_iter()
                .flatten()
                .filter(|candidate| names(candidate.def_id))
                .all(|candidate| {
                    trait_selection_inert(tcx, candidate.def_id, CandidateScope::Every, walk)
                })
    }

    /// A HIR type whose well-formedness asks nothing of a constant: a primitive, or a
    /// non-generic struct/enum/union with no predicates (also through `Self`), spelled as a
    /// plain path without generic arguments. Read through `type_of` of the named item, which
    /// lowers its HIR and evaluates nothing. Returns the type.
    fn benign_hir_ty<'tcx>(tcx: TyCtxt<'tcx>, t: &rustc_hir::Ty<'_>) -> Option<ty::Ty<'tcx>> {
        use rustc_hir::def::{DefKind, Res};
        use rustc_hir::{PrimTy, QPath, TyKind};
        let TyKind::Path(QPath::Resolved(None, path)) = t.kind else { return None };
        if !path.segments.iter().all(|seg| seg.args.is_none()) {
            return None;
        }
        let item = match path.res {
            Res::PrimTy(prim) => {
                return Some(match prim {
                    PrimTy::Bool => tcx.types.bool,
                    PrimTy::Char => tcx.types.char,
                    PrimTy::Int(it) => ty::Ty::new_int(tcx, it),
                    PrimTy::Uint(ut) => ty::Ty::new_uint(tcx, ut),
                    PrimTy::Float(ft) => ty::Ty::new_float(tcx, ft),
                    PrimTy::Str => return None,
                });
            }
            Res::SelfTyAlias { alias_to, .. } => alias_to,
            Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, did) => did,
            _ => return None,
        };
        let ty = tcx.type_of(item).instantiate_identity().skip_norm_wip();
        match ty.kind() {
            _ if is_primitive_scalar(ty) => Some(ty),
            ty::Adt(def, args)
                if args.is_empty()
                    && tcx.generics_of(def.did()).count() == 0
                    && tcx.clauses_of(def.did()).clauses.is_empty() =>
            {
                Some(ty)
            }
            _ => None,
        }
    }

    /// The leaf TYPES and the constants the leaf-shaped body names, read from its `typeck`.
    fn leaf_expr<'tcx>(
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx ty::TypeckResults<'tcx>,
        e: &rustc_hir::Expr<'_>,
        args: ty::GenericArgs<'tcx>,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_hir::def::{DefKind, Res};
        use rustc_hir::{ExprKind, UnOp};
        let Some(node_ty) = typeck.node_type_opt(e.hir_id) else { return false };
        let node_ty = ty::EarlyBinder::bind(tcx, node_ty).instantiate(tcx, args).skip_norm_wip();
        if !is_primitive_scalar(node_ty) || !typeck.expr_adjustments(e).is_empty() {
            return false;
        }
        match e.kind {
            ExprKind::Lit(_) => true,
            ExprKind::Path(ref qpath) => {
                let Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, target) =
                    typeck.qpath_res(qpath, e.hir_id)
                else {
                    return false;
                };
                let node_args = typeck.node_args(e.hir_id);
                let node_args =
                    ty::EarlyBinder::bind(tcx, node_args).instantiate(tcx, args).skip_norm_wip();
                leaf_const(tcx, target, node_args, walk)
            }
            ExprKind::Unary(UnOp::Neg | UnOp::Not, inner)
            | ExprKind::Cast(inner, _)
            | ExprKind::DropTemps(inner) => leaf_expr(tcx, typeck, inner, args, walk),
            ExprKind::Binary(_, l, r) => {
                leaf_expr(tcx, typeck, l, args, walk) && leaf_expr(tcx, typeck, r, args, walk)
            }
            ExprKind::Block(block, None) => {
                block.expr.is_some_and(|tail| leaf_expr(tcx, typeck, tail, args, walk))
            }
            // The layout call `leaf_shape` admitted (`layout_call_target`): the callee `typeck`
            // resolved is `size_of`/`align_of` itself, at a layout-primitive type.
            ExprKind::Call(callee, []) => {
                let ExprKind::Path(ref qpath) = callee.kind else { return false };
                let Res::Def(DefKind::Fn, target) = typeck.qpath_res(qpath, callee.hir_id) else {
                    return false;
                };
                if !is_layout_query_fn(tcx, target) || !typeck.expr_adjustments(callee).is_empty()
                {
                    return false;
                }
                let node_args = typeck.node_args(callee.hir_id);
                let node_args =
                    ty::EarlyBinder::bind(tcx, node_args).instantiate(tcx, args).skip_norm_wip();
                matches!(node_args.as_slice(), [arg] if arg.as_type().is_some_and(layout_primitive_ty))
            }
            _ => false,
        }
    }

    /// Inside the freeze, the first unevaluated constant in `value` that normalizing `value`
    /// would evaluate and that may NOT be evaluated here ([`may_evaluate_constant`]); `None`
    /// outside the freeze (the verifier at `optimized_mir`, where forcing CTFE is safe) or
    /// when every constant `value` names directly may be.
    ///
    /// Trust (fix11, CTFE-IN-MIR-BUILT-1). The producers normalize types they reach through a
    /// local ADT's fields — types the body's own `typeck` never normalized — and the
    /// normalizer evaluates every constant it meets. MEASURED E0391 on valid code: the THIR
    /// producer's `pointee_meta` normalized `[u8; SelfLen::K]` while building the MIR of `K`
    /// itself (`impl SelfLen { const K: usize = { let _s: Option<&SelfLen> = None; 2 }; }`).
    /// A normalization site asks this first and keeps its fail-closed answer when it
    /// answers `Some`. A constant reached only through a PROJECTION's selection or impl value
    /// is not seen here (docs/KNOWN_HAZARDS.md CTFE-IN-MIR-BUILT-1, still open for that shape).
    #[must_use]
    pub fn non_leaf_constant_if_frozen<'tcx, T: TypeVisitable<TyCtxt<'tcx>>>(
        tcx: TyCtxt<'tcx>,
        value: &T,
    ) -> Option<ty::Const<'tcx>> {
        struct NonLeaf<'tcx> {
            tcx: TyCtxt<'tcx>,
        }
        impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for NonLeaf<'tcx> {
            type Result = std::ops::ControlFlow<ty::Const<'tcx>>;
            fn visit_const(&mut self, c: ty::Const<'tcx>) -> Self::Result {
                match c.kind() {
                    ty::ConstKind::Alias(_, alias) => {
                        let leaf = alias_const_def_id(alias.kind)
                            .is_some_and(|def| may_evaluate_constant(self.tcx, def, alias.args));
                        if !leaf {
                            return std::ops::ControlFlow::Break(c);
                        }
                    }
                    // A `generic_const_exprs` expression is evaluated by normalization too.
                    ty::ConstKind::Expr(_) => return std::ops::ControlFlow::Break(c),
                    _ => {}
                }
                c.super_visit_with(self)
            }
        }
        if !frozen() || !value.has_type_flags(ty::TypeFlags::HAS_CONST_ALIAS) {
            return None;
        }
        match value.visit_with(&mut NonLeaf { tcx }) {
            std::ops::ControlFlow::Break(c) => Some(c),
            std::ops::ControlFlow::Continue(()) => None,
        }
    }

    /// Does a codegen-mode selection of the monomorphic `trait_ref` evaluate nothing? Selection
    /// CONFIRMS the where-clauses of every candidate impl it considers (winnowing evaluates
    /// each, confirmation normalizes the chosen one's), and a where-clause naming a constant
    /// (`impl P for u16 where [(); f()]: Sized`) evaluates it. Answered from the impls alone,
    /// without asking selection: the trait is neither auto nor a lang item (no built-in
    /// candidate), the self type simplifies, and every candidate — each blanket impl and each
    /// impl for that simplified self type — is inert ([`impl_is_const_inert`]). A caller whose
    /// type arguments already pass the funnel (no alias reachable through a local ADT's
    /// fields) then gets `Sized` obligations whose struct tails evaluate nothing either.
    /// `false` is the fail-closed answer.
    fn selection_is_const_inert<'tcx>(tcx: TyCtxt<'tcx>, trait_ref: ty::TraitRef<'tcx>) -> bool {
        use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
        let trait_def_id = trait_ref.def_id;
        if tcx.trait_is_auto(trait_def_id) || tcx.as_lang_item(trait_def_id).is_some() {
            return false;
        }
        let Some(simplified) = simplify_type(tcx, trait_ref.self_ty(), TreatParams::AsRigid) else {
            return false;
        };
        let impls = tcx.trait_impls_of(trait_def_id);
        impls
            .blanket_impls()
            .iter()
            .chain(impls.non_blanket_impls().get(&simplified).into_iter().flatten())
            .all(|&impl_def_id| candidate_is_const_inert(tcx, impl_def_id, trait_ref))
    }

    /// Can selecting the candidate `impl_def_id` for the monomorphic `trait_ref` evaluate a
    /// constant? Not when the impl is inert as written ([`impl_is_const_inert`]); not when its
    /// header cannot unify with `trait_ref` (selection rejects it before confirming any
    /// where-clause: `DeepRejectCtxt`, as `assemble_candidates_from_impls` asks); and not when
    /// its where-clauses, instantiated at the arguments it applies at, are each inert as written
    /// or a bound of a primitive scalar ([`primitive_trait_clause_inert`]) — `impl<T: Copy>
    /// Leaky for (T,)` at `(u32,)` confirms `u32: Copy`, which selects nothing that can
    /// evaluate. Those arguments are read by matching the impl's header against `trait_ref`
    /// ([`match_impl_arg`]) and are trusted only when the instantiated header IS `trait_ref`;
    /// a header the matcher cannot read answers `false`.
    fn candidate_is_const_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        impl_def_id: DefId,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> bool {
        // This projection caller already checked the arguments' reachable fields.
        if impl_is_const_inert(tcx, impl_def_id) {
            return true;
        }
        candidate_is_const_inert_with(tcx, impl_def_id, trait_ref, &mut |clause| {
            clause_is_inert(tcx, clause, None) || primitive_trait_clause_inert(tcx, clause)
        })
    }

    /// Same header matching as the existing CTFE gate, with an explicit clause policy.
    /// Its original caller above keeps exactly its original predicate.
    fn candidate_is_const_inert_with<'tcx>(
        tcx: TyCtxt<'tcx>,
        impl_def_id: DefId,
        trait_ref: ty::TraitRef<'tcx>,
        clause_is_safe: &mut impl FnMut(ty::Clause<'tcx>) -> bool,
    ) -> bool {
        use rustc_middle::ty::fast_reject::DeepRejectCtxt;
        // The eager next-solver preflight has no argument-funnel premise: even an
        // implicit `T: Sized` must be checked after substituting the actual ADT,
        // whose struct tail may name a projection that evaluates a constant.
        let header = tcx.impl_trait_header(impl_def_id).trait_ref;
        let identity = header.instantiate_identity().skip_norm_wip();
        if identity.args.has_aliases() {
            return false;
        }
        if !DeepRejectCtxt::relate_rigid_infer(tcx).args_may_unify(trait_ref.args, identity.args) {
            return true;
        }
        let generics = tcx.generics_of(impl_def_id);
        let mut bound: Vec<Option<ty::GenericArg<'tcx>>> = vec![None; generics.count()];
        if identity.args.len() != trait_ref.args.len()
            || !identity
                .args
                .iter()
                .zip(trait_ref.args.iter())
                .all(|(pattern, actual)| match_impl_arg(pattern, actual, &mut bound))
        {
            return false;
        }
        let mut impl_args = Vec::with_capacity(bound.len());
        for (index, arg) in bound.into_iter().enumerate() {
            match arg {
                Some(arg) => impl_args.push(arg),
                // An unbound lifetime parameter: regions select nothing.
                None if matches!(
                    generics.param_at(index, tcx).kind,
                    ty::GenericParamDefKind::Lifetime
                ) =>
                {
                    impl_args.push(tcx.lifetimes.re_erased.into())
                }
                None => return false,
            }
        }
        let impl_args = tcx.mk_args(&impl_args);
        if header.instantiate(tcx, impl_args).skip_norm_wip() != trait_ref {
            return false;
        }
        let predicates = tcx.clauses_of(impl_def_id);
        predicates.parent.is_none()
            && predicates.clauses.iter().all(|&(clause, _)| {
                let clause =
                    ty::EarlyBinder::bind(tcx, clause).instantiate(tcx, impl_args).skip_norm_wip();
                clause_is_safe(clause)
            })
    }

    /// Preflight for the next solver's eager evaluation, using only inert item/header
    /// queries. Unlike the projection gate, this also follows bounded alias-free user
    /// trait chains (including bound regions); all unmodelled builtins decline.
    pub(super) fn next_selection_is_const_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> bool {
        fn clause<'tcx>(tcx: TyCtxt<'tcx>, c: ty::Clause<'tcx>, left: &mut usize) -> bool {
            if clause_is_inert(tcx, c, None) || primitive_trait_clause_inert(tcx, c) {
                return true;
            }
            let ty::ClauseKind::Trait(pred) = c.kind().skip_binder() else { return false };
            pred.polarity == ty::ClausePolarity::Positive
                && !c.has_aliases()
                && selection(tcx, pred.trait_ref, left)
        }
        fn selection<'tcx>(tcx: TyCtxt<'tcx>, tr: ty::TraitRef<'tcx>, left: &mut usize) -> bool {
            use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
            let Some(next) = left.checked_sub(1) else { return false };
            *left = next;
            // Both solver implementations supply no builtin Clone candidate for
            // ADT Self. Only this exact concrete language item can use the ordinary
            // all-user-impl preflight below; no builtin shape or other lang item is added.
            let user_impl_only_clone = tcx.lang_items().clone_trait() == Some(tr.def_id)
                && matches!(tr.self_ty().kind(), ty::Adt(..))
                && !tr.args.has_non_region_param()
                && !tr.args.has_escaping_bound_vars()
                && primitive_copy_marker_declarations_are_inert(tcx);
            // A builtin dyn candidate also confirms superclauses and associated-type
            // bounds, which the user-impl header walk below does not inspect.
            if tr.args.has_aliases()
                || matches!(tr.self_ty().kind(), ty::Dynamic(..))
                || tr.args.has_non_region_infer()
                || tcx.def_kind(tr.def_id) != rustc_hir::def::DefKind::Trait
                || tcx.trait_is_auto(tr.def_id)
                || (tcx.as_lang_item(tr.def_id).is_some() && !user_impl_only_clone)
            {
                return false;
            }
            let Some(simple) = simplify_type(tcx, tr.self_ty(), TreatParams::AsRigid) else {
                return false;
            };
            let impls = tcx.trait_impls_of(tr.def_id);
            impls
                .blanket_impls()
                .iter()
                .chain(impls.non_blanket_impls().get(&simple).into_iter().flatten())
                .all(|&id| {
                    candidate_is_const_inert_with(tcx, id, tr, &mut |c| clause(tcx, c, left))
                })
        }
        let mut left = 256;
        param_env.caller_bounds().all(|c| clause(tcx, c, &mut left))
            && selection(tcx, trait_ref, &mut left)
    }

    /// Bind the impl parameters `pattern` (an impl header argument, identity-instantiated)
    /// names so that it becomes `actual`, structurally: a parameter binds (once, consistently),
    /// and an ADT, tuple, reference, raw pointer, array or slice recurses. Anything else must
    /// already be equal. `false` when no such binding is read here — the caller then declines,
    /// and it re-checks any binding it uses by instantiating the whole header.
    fn match_impl_arg<'tcx>(
        pattern: ty::GenericArg<'tcx>,
        actual: ty::GenericArg<'tcx>,
        bound: &mut [Option<ty::GenericArg<'tcx>>],
    ) -> bool {
        fn bind<'tcx>(
            bound: &mut [Option<ty::GenericArg<'tcx>>],
            index: u32,
            actual: ty::GenericArg<'tcx>,
        ) -> bool {
            match bound.get_mut(index as usize) {
                Some(slot @ None) => {
                    *slot = Some(actual);
                    true
                }
                Some(Some(previous)) => *previous == actual,
                None => false,
            }
        }
        match (pattern.kind(), actual.kind()) {
            (ty::GenericArgKind::Lifetime(p), ty::GenericArgKind::Lifetime(_)) => match p.kind() {
                ty::ReEarlyParam(param) => bind(bound, param.index, actual),
                _ => pattern == actual,
            },
            (ty::GenericArgKind::Const(p), ty::GenericArgKind::Const(_)) => match p.kind() {
                ty::ConstKind::Param(param) => bind(bound, param.index, actual),
                _ => pattern == actual,
            },
            (ty::GenericArgKind::Type(p), ty::GenericArgKind::Type(a)) => match (p.kind(), a.kind()) {
                (ty::Param(param), _) => bind(bound, param.index, actual),
                (ty::Adt(pd, pa), ty::Adt(ad, aa)) if pd == ad && pa.len() == aa.len() => pa
                    .iter()
                    .zip(aa.iter())
                    .all(|(p, a)| match_impl_arg(p, a, bound)),
                (ty::Tuple(pt), ty::Tuple(at)) if pt.len() == at.len() => pt
                    .iter()
                    .zip(at.iter())
                    .all(|(p, a)| match_impl_arg(p.into(), a.into(), bound)),
                (ty::Ref(pr, pt, pm), ty::Ref(ar, at, am)) if pm == am => {
                    match_impl_arg((*pr).into(), (*ar).into(), bound)
                        && match_impl_arg((*pt).into(), (*at).into(), bound)
                }
                (ty::RawPtr(pt, pm), ty::RawPtr(at, am)) if pm == am => {
                    match_impl_arg((*pt).into(), (*at).into(), bound)
                }
                (ty::Array(pt, pc), ty::Array(at, ac)) => {
                    match_impl_arg((*pt).into(), (*at).into(), bound)
                        && match_impl_arg((*pc).into(), (*ac).into(), bound)
                }
                (ty::Slice(pt), ty::Slice(at)) => match_impl_arg((*pt).into(), (*at).into(), bound),
                _ => !p.has_param() && p == a,
            },
            _ => false,
        }
    }

    /// A trait bound whose every argument is a primitive scalar or `()` (`u32: Copy`), on a
    /// trait that is not auto and is either not a lang item or `Copy`/`Clone` (whose built-in
    /// candidates over a primitive read nothing), and every impl of which selection can consider
    /// for a primitive self type — each blanket impl and each impl for a primitive — is inert
    /// as written ([`impl_is_const_inert`]). Proving it evaluates no constant.
    fn primitive_trait_clause_inert<'tcx>(tcx: TyCtxt<'tcx>, clause: ty::Clause<'tcx>) -> bool {
        let ty::ClauseKind::Trait(pred) = clause.kind().skip_binder() else { return false };
        pred.polarity == ty::ClausePolarity::Positive
            && !clause.has_aliases()
            && pred.trait_ref.args.iter().all(|arg| {
                arg.as_type().is_some_and(|t| is_primitive_scalar(t) || t.is_unit())
            })
            && primitive_trait_impls_inert(tcx, pred.def_id())
    }

    fn primitive_trait_impls_inert(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
        use rustc_attr_ir::lang_items::LangItem;
        use rustc_middle::ty::fast_reject::SimplifiedType;
        if tcx.trait_is_auto(trait_def_id)
            || tcx
                .as_lang_item(trait_def_id)
                .is_some_and(|item| !matches!(item, LangItem::Copy | LangItem::Clone))
        {
            return false;
        }
        let impls = tcx.trait_impls_of(trait_def_id);
        impls
            .blanket_impls()
            .iter()
            .chain(
                impls
                    .non_blanket_impls()
                    .iter()
                    .filter(|(key, _)| {
                        matches!(
                            key,
                            SimplifiedType::Bool
                                | SimplifiedType::Char
                                | SimplifiedType::Int(_)
                                | SimplifiedType::Uint(_)
                                | SimplifiedType::Float(_)
                                | SimplifiedType::Tuple(0)
                        )
                    })
                    .flat_map(|(_, impls)| impls.iter()),
            )
            .all(|&impl_def_id| impl_is_const_inert(tcx, impl_def_id))
    }

    /// Is every candidate a selection of `trait_def_id` can consider in `scope` inert, and are
    /// the trait's own where-clauses (`Self: Trait` aside) inert? An auto trait is never (its
    /// candidates are built in), nor, in [`CandidateScope::Every`], a lang item (which may
    /// have built-in candidates; the operator traits, asked in
    /// [`CandidateScope::PrimitiveSelf`], have none). Answers are kept for the walk.
    fn trait_selection_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        trait_def_id: DefId,
        scope: CandidateScope,
        walk: &mut LeafWalk<'tcx>,
    ) -> bool {
        use rustc_middle::ty::fast_reject::SimplifiedType;
        if let Some(&(_, _, ok)) =
            walk.traits.iter().find(|&&(d, s, _)| d == trait_def_id && s == scope)
        {
            return ok;
        }
        let ok = !tcx.trait_is_auto(trait_def_id)
            && (scope != CandidateScope::Every || tcx.as_lang_item(trait_def_id).is_none())
            && item_predicates_inert(tcx, trait_def_id, Some(trait_def_id))
            && {
                let impls = tcx.trait_impls_of(trait_def_id);
                let in_scope = |key: &SimplifiedType| {
                    scope == CandidateScope::Every
                        || matches!(
                            key,
                            SimplifiedType::Bool
                                | SimplifiedType::Char
                                | SimplifiedType::Int(_)
                                | SimplifiedType::Uint(_)
                                | SimplifiedType::Float(_)
                        )
                };
                impls
                    .blanket_impls()
                    .iter()
                    .chain(
                        impls
                            .non_blanket_impls()
                            .iter()
                            .filter(|(key, _)| in_scope(key))
                            .flat_map(|(_, impls)| impls.iter()),
                    )
                    .all(|&impl_def_id| impl_is_const_inert(tcx, impl_def_id))
            };
        walk.traits.push((trait_def_id, scope, ok));
        ok
    }

    /// A trait impl whose header and where-clauses name no alias (no projection, no constant),
    /// and whose where-clauses are inert ([`clause_is_inert`]).
    fn impl_is_const_inert(tcx: TyCtxt<'_>, impl_def_id: DefId) -> bool {
        if tcx.impl_trait_header(impl_def_id).trait_ref.skip_binder().args.has_aliases() {
            return false;
        }
        let predicates = tcx.clauses_of(impl_def_id);
        predicates.parent.is_none()
            && predicates.clauses.iter().all(|&(clause, _)| clause_is_inert(tcx, clause, None))
    }

    /// An inherent impl whose self type names no alias and whose where-clauses are inert.
    fn inherent_impl_inert(tcx: TyCtxt<'_>, impl_def_id: DefId) -> bool {
        use rustc_hir::def::DefKind;
        matches!(tcx.def_kind(impl_def_id), DefKind::Impl { of_trait: false })
            && !tcx.type_of(impl_def_id).instantiate_identity().skip_norm_wip().has_aliases()
            && {
                let predicates = tcx.clauses_of(impl_def_id);
                predicates.parent.is_none()
                    && predicates
                        .clauses
                        .iter()
                        .all(|&(clause, _)| clause_is_inert(tcx, clause, None))
            }
    }

    /// The where-clauses `typeck` registers for `def` — its own and its parents' — are inert.
    /// `trait_identity` names the trait whose `Self: Trait` clause is admitted (a trait item's
    /// predicates carry it; proving it selects the trait, which the caller checks).
    fn item_predicates_inert(tcx: TyCtxt<'_>, def: DefId, trait_identity: Option<DefId>) -> bool {
        let mut next = Some(def);
        while let Some(item) = next {
            let predicates = tcx.clauses_of(item);
            if !predicates
                .clauses
                .iter()
                .all(|&(clause, _)| clause_is_inert(tcx, clause, trait_identity))
            {
                return false;
            }
            next = predicates.parent;
        }
        true
    }

    /// Check declared bounds at the actual monomorphic trait arguments. Generic
    /// `Self: Copy` is not an inert assumption; instantiated `usize: Copy` can
    /// use the existing primitive-clause guard. The tree still solves the goal.
    pub(super) fn trait_predicates_inert_at<'tcx>(
        tcx: TyCtxt<'tcx>, trait_ref: ty::TraitRef<'tcx>,
    ) -> bool {
        if trait_ref.args.has_aliases() || trait_ref.args.has_non_region_param()
            || trait_ref.args.has_non_region_infer()
            || trait_ref.args.has_non_region_placeholders()
            || trait_ref.has_escaping_bound_vars()
        {
            return false;
        }
        let mut remaining = 256usize;
        let mut next = Some(trait_ref.def_id);
        while let Some(item) = next {
            let Some(left) = remaining.checked_sub(1) else { return false };
            remaining = left;
            let predicates = tcx.clauses_of(item);
            for &(clause, _) in predicates.clauses {
                let Some(left) = remaining.checked_sub(1) else { return false };
                remaining = left;
                // Preserve the original declaration-level inertness contract.
                // In particular generic Self: MetaSized needs no normalization;
                // inspecting its instantiated struct tail would repeat a guarded
                // written projection and reject previously supported inputs.
                // Root identity is exact across ALL original generic arguments.
                let original_root = matches!(clause.kind().no_bound_vars(),
                    Some(ty::ClauseKind::Trait(pred))
                        if pred.polarity == ty::ClausePolarity::Positive
                            && pred.trait_ref == ty::TraitRef::identity(tcx, trait_ref.def_id));
                if original_root || clause_is_inert(tcx, clause, None) {
                    continue;
                }
                let clause = ty::EarlyBinder::bind(tcx, clause)
                    .instantiate(tcx, trait_ref.args).skip_norm_wip();
                let same_root = matches!(clause.kind().no_bound_vars(),
                    Some(ty::ClauseKind::Trait(pred))
                        if pred.polarity == ty::ClausePolarity::Positive
                            && pred.trait_ref == trait_ref);
                if !same_root && !clause_is_inert(tcx, clause, None)
                    && !primitive_trait_clause_inert(tcx, clause)
                {
                    return false;
                }
            }
            next = predicates.parent;
        }
        true
    }

    /// A where-clause whose proof evaluates no constant: it names no alias (no projection,
    /// no constant), and it is an outlives bound, a `Sized`/`MetaSized`/`PointeeSized` bound
    /// whose proof reads no alias either ([`sizedness_proof_reads_no_alias`]), or the
    /// `Self: Trait` clause of `trait_identity`.
    fn clause_is_inert<'tcx>(
        tcx: TyCtxt<'tcx>,
        clause: ty::Clause<'tcx>,
        trait_identity: Option<DefId>,
    ) -> bool {
        use rustc_attr_ir::lang_items::LangItem;
        !clause.has_aliases()
            && match clause.kind().skip_binder() {
                ty::ClauseKind::RegionOutlives(_) | ty::ClauseKind::TypeOutlives(_) => true,
                // A fully evaluated primitive const already carries its exact
                // type. Checking this equality reads no body and evaluates no
                // constant; generic or deferred const typing remains refused.
                ty::ClauseKind::ConstArgHasType(constant, expected) => {
                    clause.kind().bound_vars().is_empty()
                        && !clause.has_bound_vars()
                        && exact_primitive_const_type(constant, expected)
                }
                ty::ClauseKind::Trait(pred) => {
                    (matches!(
                        tcx.as_lang_item(pred.def_id()),
                        Some(LangItem::Sized | LangItem::MetaSized | LangItem::PointeeSized)
                    ) && sizedness_proof_reads_no_alias(tcx, pred.self_ty()))
                        || (Some(pred.def_id()) == trait_identity
                            && pred.polarity == ty::ClausePolarity::Positive
                            && pred.self_ty().is_param(0))
                }
                _ => false,
            }
    }

    /// Does proving `t: Sized` (or `MetaSized`) read no alias? The proof is not local to `t`'s
    /// own flags: it follows the struct-tail chain — a struct's last field, a tuple's last
    /// element, a pattern type's base (`rustc_ty_utils` `sizedness_constraint_for_ty`,
    /// `adt_sizedness_constraint`) — and NORMALIZES the type that chain ends at, which for a
    /// projection selects its impl and confirms that impl's where-clauses. With `impl P for u16
    /// where [(); h()]: Sized { type S = u8; }` and `struct Tail { s: <u16 as P>::S }`, the
    /// alias-free clause `Tail: Sized` evaluates `h()`: MEASURED E0391 on valid code (fix11 L2
    /// review, `tests/ui/trust/sized_tail_clause_ctfe_no_query_cycle.rs`) from inside
    /// `mir_built(h)`, through the leaf gate's `typeck` and the funnel's projection reading. The
    /// chain is read with `type_of` of each tail field, unnormalized; an alias anywhere on a
    /// link, or a chain past sixteen links, answers `false`. A parameter at its end is the
    /// instantiating caller's, as for every other inert clause.
    fn sizedness_proof_reads_no_alias<'tcx>(tcx: TyCtxt<'tcx>, mut t: ty::Ty<'tcx>) -> bool {
        for _ in 0..16 {
            if t.has_aliases() {
                return false;
            }
            t = match *t.kind() {
                ty::Adt(def, args) if def.is_struct() => {
                    let Some(tail) = def.non_enum_variant().tail_opt() else { return true };
                    tcx.type_of(tail.did).instantiate(tcx, args).skip_normalization()
                }
                ty::Tuple(tys) => match tys.last() {
                    Some(&last) => last,
                    None => return true,
                },
                // The solver proves sizedness of an unsafe binder through its
                // inner type, which may itself be an ADT with a projection tail.
                ty::UnsafeBinder(bound) => {
                    tcx.instantiate_bound_regions_with_erased(bound.into())
                }
                ty::Pat(base, _) => base,
                _ => return true,
            };
        }
        false
    }

    /// May `adt`'s discriminants be computed (`discriminant_for_variant`, `discriminants`,
    /// `layout_of`) on this thread right now? Each explicit discriminant (`A = expr`) is a
    /// constant those evaluate (`eval_explicit_discr`), and no type shows it. Always outside
    /// the freeze and for a foreign enum (its discriminants are foreign constants, evaluated
    /// from metadata MIR). Inside the freeze, every explicit discriminant of a local enum must
    /// be a constant that may be evaluated here ([`may_evaluate_constant`]) — MEASURED
    /// otherwise: `enum E { A = f(), B }` with `const fn f` naming `Option<&W>`, `W` holding an
    /// `E`, was E0391 on valid code (wfcheck of `E` evaluates `f()`, whose MIR build converted
    /// `W` and computed `E`'s discriminants again;
    /// `tests/ui/trust/enum_discriminant_ctfe_no_query_cycle.rs`). A generic enum's explicit
    /// discriminant (identity arguments carry its parameters) is declined. `false` is every
    /// caller's fail-closed answer.
    #[must_use]
    pub fn discriminants_may_be_evaluated<'tcx>(tcx: TyCtxt<'tcx>, adt: ty::AdtDef<'tcx>) -> bool {
        !frozen()
            || !adt.did().is_local()
            || adt.variants().iter().all(|variant| match variant.discr {
                ty::VariantDiscr::Explicit(discr) => may_evaluate_constant(
                    tcx,
                    discr,
                    ty::GenericArgs::identity_for_item(tcx, discr),
                ),
                ty::VariantDiscr::Relative(_) => true,
            })
    }

    /// `ty` with every unevaluated constant that may be evaluated here
    /// ([`may_evaluate_constant`]: its CTFE closure is leaf, and no freeze frame on this thread
    /// forbids it) replaced by its value — the value `layout_of` itself will compute for it,
    /// through the same query. Every other constant is left in place, where the caller's
    /// own-flags check declines it as before.
    #[must_use]
    pub fn evaluate_leaf_constants<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        if !ty.has_type_flags(ty::TypeFlags::HAS_CONST_ALIAS) {
            return ty;
        }
        ty.fold_with(&mut ty::BottomUpFolder {
            tcx,
            ty_op: |t| t,
            lt_op: |r| r,
            ct_op: |c| {
                let ty::ConstKind::Alias(_, alias) = c.kind() else { return c };
                let Some(def) = alias_const_def_id(alias.kind) else { return c };
                if !may_evaluate_constant(tcx, def, alias.args) {
                    return c;
                }
                match tcx.try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    ty::Unnormalized::new_wip(c),
                ) {
                    Ok(v) if matches!(v.kind(), ty::ConstKind::Value(..)) => v,
                    _ => c,
                }
            },
        })
    }

    /// Does `ok` hold of `ty` and of every type a codegen-mode query about `ty` can reach
    /// that `ty`'s own flags do not show — the FIELDS of each LOCAL ADT `ty` names,
    /// ANYWHERE in it, recursively?
    ///
    /// `struct Inner { x: X }` with `pub type X = impl Tr;` is `ty::Adt(Inner, [])`: no
    /// alias flag anywhere on it, yet `layout_of(Inner)` lays out the field and reveals
    /// `X`. The same holds for `Option<Inner>`, `(Inner, u32)`, `[Inner; 2]` and
    /// `&Inner`: a FOREIGN ADT, a tuple or an array lays out its arguments, so the local
    /// ADT must be found wherever it sits, not only at the top (measured: a closure taking
    /// `Option<Inner>` inside `X`'s defining scope, E0391). A foreign ADT's own fields
    /// cannot name this crate's opaque except through its arguments, which the walk
    /// reaches — or through a PROJECTION over a local argument, whose local impl's
    /// where-clauses can (OPAQUE-IMPL-WHERE-LEAK-1): inside `mir_built`, in a crate that
    /// declares an opaque, such a foreign ADT's fields are walked too (`foreign_fields_ok`).
    ///
    /// Field types are read UNNORMALIZED: normalizing is the reveal being avoided, and the
    /// unnormalized field still carries the alias. Three exact readings are applied first, each
    /// asking nothing a reveal or a query cycle could hide behind: the ADT's free regions are
    /// erased before instantiation (a region bound outside the node would otherwise escape
    /// into every field), a monomorphic projection whose selected impl WROTE an alias-free
    /// value is replaced by that value (`resolve_monomorphic_projections` below; both
    /// fix10/core-refusals), and an unevaluated constant whose whole CTFE closure is leaf is
    /// replaced by its value ([`evaluate_leaf_constants`], fix11 L2). Recursion is bounded: an
    /// ADT already on the walk's stack is not re-entered (its declarations are being checked,
    /// and its arguments are on the outer type's flags), and past six nested field levels the
    /// answer is `false` — every caller's fail-closed side.
    #[must_use]
    pub fn every_reached_type<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
    ) -> bool {
        every_reached_type_at_depth(tcx, ty, 0, ok)
    }

    // Carry the original field-depth budget through selected projection arguments.
    fn every_reached_type_at_depth<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        depth: u32,
        ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
    ) -> bool {
        every_reached_type_with_memo(tcx, ty, depth, ok, &mut ClosedLayoutMemo::new(false))
    }

    fn every_reached_type_with_memo<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
        depth: u32,
        ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
        memo: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
    ) -> bool {
        fn go<'tcx>(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            depth: u32,
            stack: &mut Vec<(rustc_span::def_id::DefId, ty::Ty<'tcx>)>,
            ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
            memo: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
        ) -> bool {
            if !memo.policy_valid() { return false; }
            if memo.contains(ty) {
                return true;
            }
            let frame = memo.begin(stack.len());
            let result = go_uncached(tcx, ty, depth, stack, ok, memo);
            memo.finish(ty, frame, result);
            result
        }

        fn go_uncached<'tcx>(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            depth: u32,
            stack: &mut Vec<(rustc_span::def_id::DefId, ty::Ty<'tcx>)>,
            ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
            memo: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
        ) -> bool {
            const MAX_FIELD_DEPTH: u32 = 6;
            // A direct layout query must use the same bounded projection read as
            // this type would receive when reached through a parent's field.
            let ty = resolve_monomorphic_projections(tcx, ty, depth, memo);
            // Trust (fix11, L2): a constant whose CTFE closure is leaf is read as its value
            // (`evaluate_leaf_constants`); any other stays and is declined by `ok`.
            let ty = evaluate_leaf_constants(tcx, ty);
            if !memo.policy_valid() || !ok(ty) {
                return false;
            }
            walk_types_until(ty, |inner| {
                if !memo.policy_valid() { return false; }
                if memo.contains(inner) {
                    return true;
                }
                let ty::Adt(def, args) = inner.kind() else { return true };
                // This existing foreign boundary reads no declaration fields and
                // depends on no active ancestor, even if its DefId is active for
                // a different instantiation. Do not taint closed facts for it.
                // walk_types_until still visits every type argument below.
                if !def.did().is_local()
                    && (!leak_free_required(tcx) || !args_name_local_type(*args))
                {
                    return true;
                }
                if let Some(index) = stack.iter().position(|(id, _)| *id == def.did()) {
                    memo.backedge(index, stack[index].1 == inner);
                    return true;
                }
                if !def.did().is_local() {
                    // Trust (OPAQUE-IMPL-WHERE-LEAK-1): see `foreign_fields_ok`.
                    if leak_free_required(tcx)
                        && args_name_local_type(*args)
                        && !foreign_fields_ok(tcx, *def, *args, depth, stack, ok, memo)
                    {
                        return false;
                    }
                    return true;
                }
                if depth >= MAX_FIELD_DEPTH {
                    return false;
                }
                // Trust (fix11, L2): `layout_of` of a local ENUM also evaluates every explicit
                // discriminant, a constant no field type shows ([`discriminants_may_be_evaluated`]).
                if !discriminants_may_be_evaluated(tcx, *def) {
                    return false;
                }
                stack.push((def.did(), inner));
                // Trust (fix10/core-refusals, L3): the ADT's arguments with every FREE region
                // erased — including a region bound by a binder OUTSIDE this node (`Fm<'^0>`
                // reached inside `fn(&mut Fm<'_>)`), which would otherwise surface in every
                // instantiated field as an escaping bound var and fail the own-flags check
                // for a type `layout_of` lays out without asking about regions at all.
                // Regions select no impl and reveal nothing; a bound TYPE or CONST is left
                // in place and still declines.
                let args = ty::fold_regions(tcx, *args, |_, _| tcx.lifetimes.re_erased);
                let fields_ok = def.all_fields().all(|field| {
                    let fty = tcx.type_of(field.did).instantiate(tcx, args).skip_normalization();
                    go(tcx, fty, depth + 1, stack, ok, memo)
                });
                stack.pop();
                fields_ok
            })
        }

        /// Does `args` name a type this crate defines? A FOREIGN item instantiated only with
        /// foreign types selects only foreign impls, none of which can name this crate's
        /// opaques.
        fn args_name_local_type<'tcx>(args: ty::GenericArgs<'tcx>) -> bool {
            args.iter().filter_map(|arg| arg.as_type()).any(|t| {
                !walk_types_until(t, |inner| match inner.kind() {
                    ty::Adt(def, _) => !def.did().is_local(),
                    ty::Foreign(did)
                    | ty::FnDef(did, _)
                    | ty::Closure(did, _)
                    | ty::CoroutineClosure(did, _) => !did.is_local(),
                    _ => true,
                })
            })
        }

        /// Trust (OPAQUE-IMPL-WHERE-LEAK-1): the fields of a FOREIGN ADT whose arguments name a
        /// local type, inside `mir_built` in a crate that declares an opaque.
        ///
        /// A foreign ADT's own fields cannot name this crate's opaque, but a PROJECTION in
        /// them, instantiated with a local argument, selects a LOCAL impl:
        /// `core::iter::Peekable<L>` has the field `Option<Option<<L as Iterator>::Item>>`,
        /// whose `impl Iterator for L where Wrap<u8>: Send` the codegen-mode `layout_of` of the
        /// foreign ADT confirms, revealing `Tait` through `Wrap<u8>`'s field (E0391 inside
        /// `mir_built` of `Tait`'s defining body, `impl_where_leak_foreign_adt_by_ref.rs`).
        /// Each such field's type projections must therefore ALL resolve through
        /// `resolve_monomorphic_projections` (whose selection is the leak-free walk
        /// [`select_reveal_free`]); a local ADT they reach is checked as any reached type, and
        /// a foreign ADT nested in a field with a local argument is walked the same way. Only
        /// TYPE projections are looked at: the foreign ADT's unevaluated constants
        /// (`[MaybeUninit<K>; CAPACITY]`) are the pre-existing L2 class, unchanged here. Past
        /// sixteen nested levels the answer is `false`, the caller's decline.
        fn foreign_fields_ok<'tcx>(
            tcx: TyCtxt<'tcx>,
            def: ty::AdtDef<'tcx>,
            args: ty::GenericArgs<'tcx>,
            depth: u32,
            stack: &mut Vec<(rustc_span::def_id::DefId, ty::Ty<'tcx>)>,
            ok: &mut dyn FnMut(ty::Ty<'tcx>) -> bool,
            memo: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
        ) -> bool {
            const MAX_FOREIGN_DEPTH: u32 = 16;
            if depth >= MAX_FOREIGN_DEPTH {
                return false;
            }
            stack.push((def.did(), ty::Ty::new_adt(tcx, def, args)));
            let args = ty::fold_regions(tcx, args, |_, _| tcx.lifetimes.re_erased);
            let fields_ok = def.all_fields().all(|field| {
                let fty = tcx.type_of(field.did).instantiate(tcx, args).skip_normalization();
                let fty = if fty.has_type_flags(ty::TypeFlags::HAS_TY_PROJECTION) {
                    let resolved = resolve_monomorphic_projections(tcx, fty, depth + 1, memo);
                    if resolved.has_type_flags(ty::TypeFlags::HAS_TY_PROJECTION) {
                        return false;
                    }
                    resolved
                } else {
                    fty
                };
                walk_types_until(fty, |inner| {
                    if !memo.policy_valid() { return false; }
                if memo.contains(inner) {
                        return true;
                    }
                    if let ty::Adt(inner_def, inner_args) = inner.kind() {
                        // As above, a foreign declaration with no local type
                        // arguments is not read, so its success is independent
                        // of any same-DefId ancestor. Keep visiting arguments.
                        if !inner_def.did().is_local() && !args_name_local_type(*inner_args) {
                            return true;
                        }
                        if let Some(index) = stack.iter().position(|(id, _)| *id == inner_def.did()) {
                            memo.backedge(index, stack[index].1 == inner);
                            return true;
                        }
                    }
                    match inner.kind() {
                    ty::Adt(inner_def, _) if inner_def.did().is_local() => {
                        go(tcx, inner, depth + 1, stack, ok, memo)
                    }
                    ty::Adt(inner_def, inner_args) => {
                        !args_name_local_type(*inner_args)
                            || foreign_fields_ok(tcx, *inner_def, *inner_args, depth + 1, stack, ok, memo)
                    }
                    _ => true,
                    }
                })
            });
            stack.pop();
            fields_ok
        }

        /// Every MONOMORPHIC projection in the field type `fty` replaced by the value the
        /// impl a codegen-mode `layout_of` would select WROTE for it — and only when that
        /// value can be read without normalizing anything (Trust, fix10/core-refusals, L1).
        /// Any projection this does not resolve is left in place, where the caller's
        /// own-flags check declines it exactly as before.
        ///
        /// `struct Atomic<T: AtomicPrimitive> { v: UnsafeCell<T::Storage> }` at `T = bool`
        /// has the field `UnsafeCell<<bool as AtomicPrimitive>::Storage>`: an alias, so the
        /// funnel declined `layout_of(Atomic<bool>)` — although `layout_of` resolves it to
        /// `Align1<u8>` by selecting the one impl and reading what it wrote. Reading it
        /// here asks no more than the funnel already lets through elsewhere:
        ///
        ///   * the SELECTION is `codegen_select_candidate` over a trait reference whose every
        ///     type argument passes the funnel itself (deep, at the next depth) and which
        ///     names no alias at all — the same admission
        ///     `tuple_layouts::resolution_may_reenter` gives `Instance::try_resolve`, which
        ///     runs this same query. No opaque, coroutine or alias is reachable from what is
        ///     selected over — but the selected impl's WHERE-CLAUSES can name one, so inside
        ///     `mir_built`, in a crate that declares an opaque, the selection is
        ///     [`select_reveal_free`]'s leak-free walk instead (OPAQUE-IMPL-WHERE-LEAK-1);
        ///   * the VALUE is `type_of` of the selected impl's own item — what the impl WROTE,
        ///     the read `projection_reaches_opaque` makes for the same reason — instantiated
        ///     with the impl arguments, and accepted only when it carries NO alias of any
        ///     kind: an opaque (`type Storage = impl Tr`), a nested projection, or an
        ///     unevaluated constant (`[u8; N]`) is declined, so no reveal is ever started —
        ///     except a constant whose CTFE closure is leaf (fix11, L2:
        ///     [`evaluate_leaf_constants`]), which is read as its value first;
        ///   * a `default` item, an item the selected impl does not itself define (inherited
        ///     from a specialization parent or the trait default), a generic associated type,
        ///     a return-position-impl-trait-in-trait item, and every non-user-written impl
        ///     source (builtin, param, object) decline.
        ///
        /// The caller re-checks the RESULT with its own predicate and walks its local ADTs,
        /// so what this returns is never trusted further than the unnormalized field was.
        fn resolve_monomorphic_projections<'tcx>(
            tcx: TyCtxt<'tcx>,
            fty: ty::Ty<'tcx>,
            depth: u32,
            memo: &mut ClosedLayoutMemo<ty::Ty<'tcx>>,
        ) -> ty::Ty<'tcx> {
            if !fty.has_type_flags(ty::TypeFlags::HAS_TY_PROJECTION) {
                return fty;
            }
            fty.fold_with(&mut ty::BottomUpFolder {
                tcx,
                ty_op: |t| match t.kind() {
                    ty::Alias(_, alias) => {
                        let policy = ProjectionRhsPolicy::LeafConstants;
                        // Only a fully completed reader result from this exact
                        // context/policy can avoid new reader work. The caller
                        // still walks the returned type at its carried depth.
                        let read = memo.completed_projection(t, policy)
                            .map(|(value, written)| ReadProjection { value, written })
                            .or_else(|| read_monomorphic_projection_with_memo(
                                tcx, *alias, depth, memo, policy,
                            ));
                        match read {
                            Some(read) => {
                                // Exact alias passed to the reader after child rewrites,
                                // and its independently guarded written RHS. Original nested
                                // aliases without this exact key remain unsupported.
                                // Keep the pre-evaluation data: an evaluated type is not a
                                // raw-source inertness witness.
                                memo.record_completed_projection(t, policy, read.value, read.written);
                                memo.record_written_projection(t, read.written);
                                read.value
                            }
                            None => t,
                        }
                    },
                    _ => t,
                },
                lt_op: |r| r,
                ct_op: |c| c,
            })
        }


        go(tcx, ty, depth, &mut Vec::new(), ok, memo)
    }

    // The layout funnel and type-specific producer fallback share this exact reader.
    // Keep its selection, argument walk, defaultness and leaf-constant gates together.
    fn read_monomorphic_projection<'tcx>(
        tcx: TyCtxt<'tcx>,
        alias: ty::AliasTy<'tcx>,
        depth: u32,
    ) -> Option<ty::Ty<'tcx>> {
        read_monomorphic_projection_with_memo(
            tcx, alias, depth, &ClosedLayoutMemo::new(false), ProjectionRhsPolicy::LeafConstants,
        ).map(|read| read.value)
    }

    struct ReadProjection<'tcx> {
        value: ty::Ty<'tcx>,
        written: ty::Ty<'tcx>,
    }

    fn read_monomorphic_projection_with_memo<'tcx>(
        tcx: TyCtxt<'tcx>,
        alias: ty::AliasTy<'tcx>,
        depth: u32,
        memo: &ClosedLayoutMemo<ty::Ty<'tcx>>,
        rhs_policy: ProjectionRhsPolicy,
    ) -> Option<ReadProjection<'tcx>> {
        const MAX_FIELD_DEPTH: u32 = 6;
        let ty::AliasTyKind::Projection { def_id } = alias.kind else { return None };
        let assoc: rustc_span::def_id::DefId = def_id.into();
        if depth >= MAX_FIELD_DEPTH
            || tcx.is_impl_trait_in_trait(assoc)
            || alias.args.has_aliases()
            || alias.args.has_non_region_param()
            || alias.args.has_non_region_infer()
            || alias.args.has_non_region_placeholders()
            || alias.args.has_escaping_bound_vars()
        {
            return None;
        }
        let trait_def_id = tcx.parent(assoc);
        // A generic associated type carries own arguments past the trait's.
        if alias.args.len() != tcx.generics_of(trait_def_id).count() {
            return None;
        }
        // Selection must have nothing to reveal: every type argument passes the funnel,
        // deep, with the depth carried on so a type that names itself through a
        // projection argument (`struct S { f: <Box<S> as Tr>::A }`) terminates.
        let mut argument = memo.argument_scope();
        for arg in alias.args.types() {
            if !every_reached_type_with_memo(tcx, arg, depth + 1, &mut |t| {
                layout_query_is_reentrant_safe(t)
            }, &mut argument) {
                return None;
            }
        }
        let args = tcx.erase_and_anonymize_regions(alias.args);
        let trait_ref = ty::TraitRef::new_from_args(tcx, trait_def_id, args);
        // Trust (fix11, CTFE-IN-MIR-BUILT-1): selection confirms the candidates'
        // where-clauses, and one that names a constant evaluates it — MEASURED E0391 on
        // valid code from this very call (`impl P for u16 where [(); f()]: Sized { type S
        // = u8; }`, `struct W { s: <u16 as P>::S }`, `const fn f` naming `W`: building
        // `f`'s MIR -> "computing candidate for `<u16 as P>`" -> evaluating `f()`). Inside
        // the freeze, select only when no candidate can evaluate anything.
        if frozen() && !selection_is_const_inert(tcx, trait_ref) {
            return None;
        }
        // Trust (OPAQUE-IMPL-WHERE-LEAK-1): the selection's NESTED obligations are the
        // impl's where-clauses, which name what they like however clean the arguments
        // checked above are: `impl<T> Prim for T where Wrap<T>: Send` with `struct Wrap<T>
        // { t: T, x: Tait }`, or `impl Prim for u8 where Tait: Debug`. A codegen-mode
        // selection reveals `Tait` for either (`Wrap<u8>: Send` through its field, `Tait:
        // Debug` by normalizing it), borrow-checking its defining body, possibly the one
        // being built: E0391 on valid Rust (`impl_where_leak_boxed.rs`,
        // `impl_where_leak_nonauto_where.rs`). Inside `mir_built`, in a crate that declares
        // an opaque, the selection is walked leak-free instead ([`select_reveal_free`]),
        // and a where-clause that names an opaque anywhere in the walk leaves the
        // projection in place for the caller to decline. The codegen-mode `layout_of` the
        // deep guard then admits re-selects the same impls through the same where-clauses.
        let source = if leak_free_required(tcx) {
            // Input facts describe only independently completed type walks.
            // The next-solver owner separately inventories raw declarations;
            // all selection, where-clause and proof-tree refusals still run.
            if argument.is_empty() {
                select_projection_reveal_free(tcx, ty::ParamEnv::empty(), trait_ref)?
            } else {
                if !next_solver_reveal_free::prepare_input_bindings(tcx, trait_ref, &mut argument) {
                    return None;
                }
                select_reveal_free_in_mode(
                    tcx, ty::ParamEnv::empty(), trait_ref, false, Some(&argument),
                )?
            }
        } else {
            tcx.codegen_select_candidate(
                ty::TypingEnv::fully_monomorphized().as_query_input(trait_ref),
            )
            .ok()?
            .clone()
        };
        let rustc_middle::traits::ImplSource::UserDefined(data) = source else {
            return None;
        };
        if tcx.defaultness(data.impl_def_id).is_default() {
            return None;
        }
        let item = *tcx.impl_item_implementor_ids(data.impl_def_id).get(&assoc)?;
        if tcx.defaultness(item).is_default()
            || tcx.generics_of(item).count() != data.args.len()
        {
            return None;
        }
        let written = tcx.type_of(item).instantiate(tcx, data.args).skip_normalization();
        // Trust (fix11, L2): a leaf-closure constant in the value (`[u8; LEN]`) is read
        // as its value, exactly as in a field; any other constant stays and declines.
        let value = match rhs_policy {
            ProjectionRhsPolicy::LeafConstants => evaluate_leaf_constants(tcx, written),
            ProjectionRhsPolicy::WrittenOnly => written,
        };
        (!value.has_aliases()
            && !value.has_non_region_param()
            && !value.has_non_region_infer()
            && !value.has_non_region_placeholders()
            && !value.has_escaping_bound_vars())
        .then_some(ReadProjection { value, written })
    }

    /// Independent foreign metadata custody, not a retry of a refused layout.
    /// Primitive value-only inputs and exclusively foreign candidate impls cannot
    /// reach a current-crate MIR body. Keep every ordinary reader/selection guard,
    /// use its LAST permitted depth (5, arguments 6), and never evaluate the RHS.
    /// The caller charges this preparation separately from raw input verification.
    fn read_foreign_written_projection<'tcx>(
        tcx: TyCtxt<'tcx>,
        source: ty::Ty<'tcx>,
        remaining: &mut usize,
    ) -> Option<ty::Ty<'tcx>> {
        use rustc_middle::ty::fast_reject::{TreatParams, simplify_type};
        let ty::Alias(_, alias) = source.kind() else { return None };
        let ty::AliasTyKind::Projection { def_id } = alias.kind else { return None };
        let assoc: DefId = def_id.into();
        let trait_def = tcx.parent(assoc);
        if !matches!(tcx.def_kind(trait_def), rustc_hir::def::DefKind::Trait)
            || assoc.is_local() || trait_def.is_local()
            || alias.args.is_empty() || alias.args.has_aliases() {
            return None;
        }
        for arg in alias.args {
            *remaining = remaining.checked_sub(1)?;
            let inert = match arg.kind() {
                ty::GenericArgKind::Lifetime(_) => true,
                ty::GenericArgKind::Type(t) => next_solver_reveal_free::primitive_input(t, remaining),
                ty::GenericArgKind::Const(c) => matches!(c.kind(), ty::ConstKind::Value(value)
                    if is_primitive_scalar(value.ty)),
            };
            if !inert { return None }
        }
        let simplified = simplify_type(tcx, alias.args.type_at(0), TreatParams::AsRigid)?;
        let impls = tcx.trait_impls_of(trait_def);
        for &candidate in impls.blanket_impls().iter().chain(
            impls.non_blanket_impls().get(&simplified).into_iter().flatten(),
        ) {
            *remaining = remaining.checked_sub(1)?;
            if candidate.is_local() { return None }
        }
        read_monomorphic_projection_with_memo(
            tcx, *alias, 5, &ClosedLayoutMemo::new(false), ProjectionRhsPolicy::WrittenOnly,
        ).map(|read| read.written)
    }

    /// Source-bound addressable storage geometry. This proves no initialized
    /// value, active union field, drop behavior, ABI, provenance or permission.
    /// Construction is confined to this compiler's actual MaybeUninit lang item
    /// and exact immutable TyCtxt; the source and payload types are retained.
    pub struct CheckedMaybeUninitStorage<'tcx> {
        source: ty::Ty<'tcx>,
        payload: ty::Ty<'tcx>,
        size: u64,
        align: u64,
        pointer_bits: u32,
    }

    impl<'tcx> CheckedMaybeUninitStorage<'tcx> {
        pub fn source(&self) -> ty::Ty<'tcx> { self.source }
        pub fn payload(&self) -> ty::Ty<'tcx> { self.payload }
        pub fn size_bytes(&self) -> u64 { self.size }
        pub fn align_bytes(&self) -> u64 { self.align }
        pub fn pointer_bits(&self) -> u32 { self.pointer_bits }
    }

    /// Exact addressable geometry of an actual Rust union declaration. This is
    /// distinct from the MaybeUninit lang-item/payload witness above: no active
    /// field, initialized value, drop, ABI or access permission is established.
    pub struct CheckedUnionStorage<'tcx> {
        source: ty::Ty<'tcx>,
        size: u64,
        align: u64,
        pointer_bits: u32,
    }

    impl<'tcx> CheckedUnionStorage<'tcx> {
        pub fn source(&self) -> ty::Ty<'tcx> { self.source }
        pub fn size_bytes(&self) -> u64 { self.size }
        pub fn align_bytes(&self) -> u64 { self.align }
        pub fn pointer_bits(&self) -> u32 { self.pointer_bits }
    }

    /// Bounded query-safety scratch owned by one compiler consumer. This is not
    /// a layout, trait verdict or certificate. Only independently closed pure
    /// layout facts survive calls; no active ancestor assumption is exported.
    /// The immutable TyCtxt is fixed at construction, and any freeze transition
    /// invalidates all retained facts, even when the original stack is restored.
    pub struct LayoutQuerySafetyContext<'tcx> {
        tcx: TyCtxt<'tcx>,
        epoch: Cell<Option<u64>>,
        memo: RefCell<ClosedLayoutMemo<ty::Ty<'tcx>>>,
        // The freeze policy belongs to this thread, not just to the TyCtxt.
        _thread: std::marker::PhantomData<std::rc::Rc<()>>,
    }

    impl<'tcx> LayoutQuerySafetyContext<'tcx> {
        #[must_use]
        pub fn new(tcx: TyCtxt<'tcx>) -> Self {
            Self {
                tcx,
                epoch: Cell::new(FREEZE_EPOCH.with(Cell::get)),
                memo: RefCell::new(ClosedLayoutMemo::for_epoch(freeze_epoch(), freeze_epoch)),
                _thread: std::marker::PhantomData,
            }
        }

        /// Retain the exact source union's sized byte geometry only. All fields
        /// overlap at offset zero; no field is chosen or observed. Layout is
        /// queried only through the unchanged bounded safety/epoch policy.
        pub fn union_storage(&self, source: ty::Ty<'tcx>) -> Option<CheckedUnionStorage<'tcx>> {
            let epoch = freeze_epoch()?;
            let tcx = self.tcx;
            let ty::Adt(def, _) = source.kind() else { return None };
            if !def.is_union() || !self.is_safe(source) { return None; }
            let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(source)).ok()?;
            let fields = &def.non_enum_variant().fields;
            if fields.is_empty() || layout.fields.count() != fields.len()
                || (0..fields.len()).any(|index| layout.fields.offset(index).bytes() != 0) {
                return None;
            }
            let size = layout.size.bytes();
            let align = layout.align.bytes();
            let pointer_bits = tcx.data_layout.pointer_size().bits() as u32;
            if !matches!(pointer_bits, 32 | 64) || !align.is_power_of_two() || size % align != 0
                || (pointer_bits == 32 && (size > u64::from(u32::MAX) || align > (1_u64 << 31)))
                || size.checked_mul(8).is_none() || align.checked_mul(8).is_none()
                || freeze_epoch() != Some(epoch) {
                return None;
            }
            Some(CheckedUnionStorage { source, size, align, pointer_bits })
        }

        /// Bind the ACTUAL compiler lang-item union and its ManuallyDrop<T>
        /// field to rustc's exact sized layout. No payload is selected or read.
        /// Every query uses the existing pure safety context; policy transitions
        /// throughout this construction refuse the witness.
        pub fn maybe_uninit_storage(
            &self, source: ty::Ty<'tcx>,
        ) -> Option<CheckedMaybeUninitStorage<'tcx>> {
            let epoch = freeze_epoch()?;
            let tcx = self.tcx;
            let ty::Adt(def, args) = source.kind() else { return None };
            if !def.is_union() || tcx.lang_items().maybe_uninit() != Some(def.did())
                || args.len() != 1 {
                return None;
            }
            let ty::GenericArgKind::Type(payload) = args.iter().next()?.kind() else { return None };
            if !self.is_safe(source) || !self.is_safe(payload) { return None; }
            let fields = &def.non_enum_variant().fields;
            if fields.len() != 2 { return None; }
            let mut dataless = false;
            let mut wrapped = None;
            for field in fields {
                let field_ty = field.ty(tcx, *args).skip_normalization();
                if field_ty.is_unit() {
                    if dataless { return None; }
                    dataless = true;
                } else {
                    let ty::Adt(wrapper, wrapper_args) = field_ty.kind() else { return None };
                    if wrapped.is_some() || !wrapper.is_manually_drop() || !wrapper.is_struct()
                        || wrapper_args.len() != 1
                        || !matches!(wrapper_args.iter().next()?.kind(), ty::GenericArgKind::Type(t) if t == payload) {
                        return None;
                    }
                    let wrapper_fields = &wrapper.non_enum_variant().fields;
                    if wrapper_fields.len() != 1
                        || wrapper_fields.iter().next()?.ty(tcx, *wrapper_args).skip_normalization() != payload
                        || !self.is_safe(field_ty) {
                        return None;
                    }
                    wrapped = Some(field_ty);
                }
            }
            if !dataless { return None; }
            let wrapped = wrapped?;
            let env = ty::TypingEnv::fully_monomorphized();
            let layout = tcx.layout_of(env.as_query_input(source)).ok()?;
            let payload_layout = tcx.layout_of(env.as_query_input(payload)).ok()?;
            let wrapped_layout = tcx.layout_of(env.as_query_input(wrapped)).ok()?;
            if wrapped_layout.fields.count() != 1 || wrapped_layout.fields.offset(0).bytes() != 0
                || wrapped_layout.size != payload_layout.size || wrapped_layout.align != payload_layout.align
                || layout.size != payload_layout.size || layout.align != payload_layout.align
                || layout.fields.count() != 2
                || (0..2).any(|index| layout.fields.offset(index).bytes() != 0) {
                return None;
            }
            let size = layout.size.bytes();
            let align = layout.align.bytes();
            let pointer_bits = tcx.data_layout.pointer_size().bits() as u32;
            if !matches!(pointer_bits, 32 | 64) || !align.is_power_of_two() || size % align != 0
                || (pointer_bits == 32 && (size > u64::from(u32::MAX) || align > (1_u64 << 31)))
                || size.checked_mul(8).is_none()
                || align.checked_mul(8).is_none() || freeze_epoch() != Some(epoch) {
                return None;
            }
            Some(CheckedMaybeUninitStorage { source, payload, size, align, pointer_bits })
        }

        /// Check the original bounded guard, reusing completed facts only under
        /// the exact same immutable environment and uninterrupted policy epoch.
        #[must_use]
        pub fn is_safe(&self, ty: ty::Ty<'tcx>) -> bool {
            let epoch = FREEZE_EPOCH.with(Cell::get);
            let Ok(mut memo) = self.memo.try_borrow_mut() else {
                // Reentry cannot borrow another call's active frames.
                return layout_query_is_reentrant_safe_deep(self.tcx, ty);
            };
            if epoch.is_none() || self.epoch.get() != epoch {
                *memo = ClosedLayoutMemo::for_epoch(freeze_epoch(), freeze_epoch);
                self.epoch.set(epoch);
            }
            let answer = every_reached_type_with_memo(
                self.tcx, ty, 0, &mut |t| layout_query_is_reentrant_safe(t), &mut memo,
            );
            if epoch.is_none() || FREEZE_EPOCH.with(Cell::get) != epoch {
                *memo = ClosedLayoutMemo::for_epoch(freeze_epoch(), freeze_epoch);
                self.epoch.set(FREEZE_EPOCH.with(Cell::get));
                return false;
            }
            answer
        }
    }

    /// May a codegen-mode query (`layout_of`, `Instance::try_resolve`, an auto trait) be
    /// asked about `ty` from inside `mir_built`? [`layout_query_is_reentrant_safe`] of
    /// every type [`every_reached_type`] reaches (#48).
    #[must_use]
    pub fn layout_query_is_reentrant_safe_deep<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
        // Trust: summaries never escape this exact immutable TyCtxt/policy walk.
        // Only this pure layout predicate enables reuse; general callback walks
        // retain their original visitation and all original depth/refusal gates.
        let epoch = freeze_epoch();
        let answer = every_reached_type_with_memo(
            tcx, ty, 0, &mut |t| layout_query_is_reentrant_safe(t),
            &mut ClosedLayoutMemo::for_epoch(epoch, freeze_epoch),
        );
        answer && epoch.is_some() && freeze_epoch() == epoch
    }
}
pub mod atomic_callsite;
pub mod concurrency_effects;
mod constant_image;
mod convert;
pub mod instance_body;
pub mod nominal_parameter;
pub mod nominal_body;
pub mod nominal_capture;
pub use convert::debug_finisher_names_have_fields;
pub use convert::debug_fixed_finisher_forwards_inputs;
pub use convert::function_is_borrow_provenance_clean;
pub use convert::immutable_operand_const;
pub use convert::std_adapter_total_panic_free;
// THE AUTHENTICATED ANSWER to "is this span inside the real standard library",
// for the consumer that holds no `TyCtxt`. See the function's own note for the
// measured defect (a directory name deleting an unsafe deref's obligations)
// that it closes.
pub use convert::trusted_std_source_files;
pub use ty_convert::is_authenticated_bignum_crate;
pub use ty_convert::is_authenticated_serde_json_crate;
pub use convert::{
    CertifiedPairedCondvarWaitCallSite, collect_certified_paired_condvar_wait_calls,
    // THE CALLEE'S IDENTITY, for a consumer that holds `(TyCtxt, DefId)` and
    // would otherwise have to read a RENDERING of them. The unsafe-call
    // completeness check in `rustc_mir_transform::trust_verify` is that
    // consumer: it had only `safe_def_path_str(tcx, did)` to decide with, and
    // for a LOCAL callee that string is the USER'S OWN PATH.
    callee_key_for,
    // Trust (2026-10-10, CALL-REACH-1 D1): the identity the extractor stamps on a
    // call, minted by the compiler's call-reach record from the same `(DefId,
    // args)` so the bridge's withdrawal lookup is by instance, never by rendering.
    callee_identity_for,
    func_operand_name, func_operand_name_in_body, is_derived_total_method,
    is_diverging_panic_or_abort_terminal,
    is_total_derived_trait_call, panic_free_intrinsic_mint_selftest,
    tcx_is_authenticated_core_integer_wrapping_method, tcx_is_authenticated_e6_arithmetic_method,
    trust_try_total_marker,
};
// DROP-NAME-COLLIDE-1 (2026-10-03): THE duplicate-crate-name rule. The compiler's
// structural drop-credit collection and its X1 destructor-admission shadow check
// read it here, the extractor's callee and by-name-marker disambiguation read it
// in `convert`/`ty_convert`, so the consumers of a crate-NAME-keyed rendered path
// cannot drift apart.
pub use convert::crate_name_is_shared;
// Trust (ARGS-FINGERPRINT-READ-1 round 3): whether a local fn's definition key is
// rendered by another local fn too; the compiler's direct-self-call identity set
// reads it.
pub use convert::local_fn_definition_key_is_shared;
// Research-only backward slicing for VC minimization. No production caller
// consumes the sliced body yet, so compiling this sizeable analysis into
// trustc only adds build time and an accidentally-advertised integration
// surface. Keep its adversarial unit tests without shipping unwired code.
#[cfg(test)]
mod slicing;
// verifier-perf: cheap fast-reject classifier so the verifier
// pass can skip lowering on functions it provably can't handle.
pub mod supportability;
// per-crate policy bucketing — decides whether the verifier
// should generate proof obligations on a function or boundary-extract
// only. Pairs with supportability::classify for the two-axis decision.
pub mod policy;
mod ty_convert;
// Trust (2026-09-29): rustc's tuple layouts on the faithful lane.
mod tuple_layouts;
// Trust (ALLOC-STRIDE-ADT-2, 2026-10-07): rustc's element sizes for the verifier
// lane, as a side table outside the extracted function.
mod elem_sizes;
mod primitive_decimal_strings;
mod ty_frontier;
mod verifier_api;
// Trust (D8, 2026-09-24): the ONE predicate for "a `Box` returned by this call
// is a validity root", shared by the extractor's assert discharge and (via the
// compiler-supplied block set) trust-vcgen's separation engine.
mod returned_box_root;
pub use returned_box_root::returned_box_root_call_blocks;
// Trust #soundness (VS-1 follow-up, 2026-10-04): a loop clause binds the source
// binding in scope at its loop, or it binds nothing.
mod loop_clause_binding;
pub use loop_clause_binding::refuse_loop_clauses_bound_outside_their_scope;

use std::sync::Arc;

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::AttributeKind;
use rustc_hir::def::DefKind;
use rustc_middle::mir;
use rustc_middle::mir::trust_contract as rustc_trust_contract;
use rustc_middle::ty::print::{
    with_def_path_disambiguators, with_no_trimmed_paths, with_no_visible_paths,
    with_resolve_crate_name,
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::Symbol;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;

/// Invocation-scoped diagnostic identity for contract assumptions that were
/// deliberately dropped.  One MIR body is extracted at several independent
/// verifier seams (root verification, R1 analysis, and native bundling).  Those
/// consumers must all recompute the fail-closed gate, but they must not each
/// report the same source-level warning.  Compiletest deliberately disables the
/// diagnostic engine's generic deduplication, so make this ownership explicit.
///
/// Session storage is load-bearing: a process embedding rustc may compile more
/// than one crate, and a process-global cache could suppress a later Session's
/// diagnostics.  Distinct reasons remain distinct; only an exact
/// `(definition, reason)` replay is coalesced.
#[derive(Default)]
struct SessionContractAssumptionWarnings {
    emitted: FxHashSet<(DefId, contract_assumption_gate::AssumeSkipReason)>,
}

/// Trust (M0(c) follow-up, 2026-09-30): the definitions whose authored
/// preconditions the assumption gate DROPPED from their body verification
/// (`contract_assumption_gate::gate_contract_preconditions` returned a skip
/// reason). The gate drops the whole contract-derived set on any failure, so a
/// definition absent from this set had every authored `requires` assumed as a body
/// hypothesis.
///
/// Its own session state, not [`SessionContractAssumptionWarnings`]: that table
/// exists to de-duplicate a diagnostic, and a proof-relevant fact must not ride on
/// a warning's bookkeeping.
#[derive(Default)]
struct SessionContractPreconditionsDropped {
    definitions: FxHashSet<DefId>,
}

/// Did the assumption gate keep EVERY authored precondition of `def_id` as a body
/// hypothesis? `false` once the gate dropped them. The typed-CHC encoding-fidelity
/// attestation reads this: a counterexample to a postcondition is a call the
/// function can receive only if the payload carries the preconditions a caller is
/// bound by.
///
/// Meaningful only after `def_id` was extracted in this session, which
/// verification of `def_id` always does first.
pub fn contract_preconditions_all_assumed(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !tcx.sess.with_trust_compiler_state::<SessionContractPreconditionsDropped, _>(|state| {
        state.definitions.contains(&def_id)
    })
}

fn first_contract_assumption_warning(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    reason: &contract_assumption_gate::AssumeSkipReason,
) -> bool {
    if tcx.sess.with_trust_compiler_state::<SessionNoBodyVerification, _>(|state| state.declared)
    {
        return false;
    }
    tcx.sess.with_trust_compiler_state::<SessionContractAssumptionWarnings, _>(|state| {
        state.emitted.insert((def_id, reason.clone()))
    })
}

/// Trust (TG3, COMPILE-TIME-FACTS-1): set by the kernel-only lane of a
/// `-Ztrust-verify=off` session, which extracts bodies for E6 kernel import and
/// runs no body verification. The assumption gate still drops what it drops (that
/// is fail-closed and changes nothing a kernel import reads), but its warning, "not
/// assumed for body verification", would describe a verification that does not run.
#[derive(Default)]
struct SessionNoBodyVerification {
    declared: bool,
}

/// Declare that this session runs no body verification (the kernel-only lane of
/// `-Ztrust-verify=off`): the contract-assumption warning is then not emitted.
pub fn declare_no_body_verification(tcx: TyCtxt<'_>) {
    tcx.sess.with_trust_compiler_state::<SessionNoBodyVerification, _>(|state| {
        state.declared = true;
    });
}
#[allow(deprecated)]
pub use verifier_api::{
    TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY, VerifierVcContentIdentity,
    contract_bundle_to_verifier_api, contract_bundle_to_verifier_api_with_compiler_identity,
    contract_bundle_to_verifier_api_with_crate_name, function_to_verifier_api_bundle,
    function_to_verifier_api_bundle_with_compiler_identity,
    function_to_verifier_api_bundle_with_crate_name,
    function_to_verifier_api_bundle_with_loop_feedback_candidates,
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity,
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name,
    verifier_api_emitted_vc_indices, verifier_api_source_clause_body_formula_metadata,
    verifier_source_digest, verifier_vc_content_identity,
    verifier_vc_content_identity_with_crate_name, verifier_vc_content_identity_with_source_digest,
    verifier_vc_content_identity_with_source_digest_and_crate_name,
};

/// Return a crate-qualified, definition-site path without triggering the
/// `trimmed_def_paths` query.
///
/// Trust uses this string as a semantic routing identity, so it must neither
/// omit the local crate nor select a context-dependent visible re-export.
///
/// # THE ONE RENDERING SEAM — a NARROWING, **NOT** an injectivity guarantee
///
/// This function and [`safe_def_path_str_with_args`] are the PRIMARY producers
/// of Trust's def-path identity space: the callee key (`convert::func_operand_name`),
/// the bundled-body key (`VerifiableFunction::def_path`), every
/// contract-summary key, and every panic-freedom / expected-absent / assumed-total
/// / ABI-total discharge set. Routing what CAN be discriminated through HERE,
/// rather than adding a check at each consumer, is deliberate — per-consumer
/// checks are the shape that kept failing (see the `direct_call_def_path` doc
/// comment for the exploited history).
///
/// "PRIMARY", not "only", and the distinction is load-bearing: this claim was
/// shipped as "the ONLY producers" and refuted by measurement. Do not rebuild
/// an argument on producer-exclusivity without re-establishing it — verify by
/// grepping the `def_path_str` family, not by trusting this sentence.
///
/// **Do not read this string as an identity.** `with_def_path_disambiguators`
/// removes three MEASURED collision classes: same-named siblings **in the same
/// namespace**, a foreign import merging into its `extern` block's GRANDPARENT
/// namespace, and a type parameter named after a primitive. It leaves at least
/// FIVE, ENUMERATED on `direct_call_def_path`. Residual 1 is still open in the
/// render: a call from a generic body prints like a generic definition. It is
/// closed fail-closed only at the call-site name (`func_operand_name` tags it;
/// GENERIC-CALL-KEY-ALIAS-1), so a consumer that renders a call key here instead
/// still gets the aliasing string. Any new consumer must still be safe when two
/// distinct things arrive under one key.
///
/// The namespace qualifier is load-bearing, not hedging.
/// `DefPathData::TypeNs(sym)` and `DefPathData::ValueNs(sym)` are DIFFERENT
/// variants and the disambiguator counter is keyed on `(parent, DefPathData)`,
/// so a `fn S` and a `struct S` under one parent are BOTH `#0` and the
/// DISAMBIGUATOR still renders both `S`. That class is §RESIDUAL 7 and it is
/// CLOSED — not by the disambiguator, which cannot reach it, but one frame out
/// by [`apply_cross_namespace_tag`], which is applied to the output of both
/// renderers below. This paragraph said "MEASURED OPEN" for two days after the
/// tag had landed; see the correction note on `apply_cross_namespace_tag`.
///
/// # What moves, and what a consumer may rely on
///
/// Two of the three closures move ONLY previously-ambiguous spellings: a
/// `DisambiguatedDefPathData` disambiguator is nonzero only when an earlier
/// sibling shares the same `(parent, DefPathData)`, and the `ty::ParamTy` marker
/// fires only on a parameter whose name is a primitive. Note that the same
/// sentence bounds what the disambiguator can REACH: siblings under different
/// `DefPathData` variants are never counted together — that is §RESIDUAL 7, and
/// it is handled by [`apply_cross_namespace_tag`], not by this closure.
///
/// There is a FOURTH mover, and it does NOT have that property either: the
/// cross-namespace tag applied below is a suffix over the whole `DefPath` chain,
/// so it moves an UNAMBIGUOUS local path whenever an ancestor segment is the
/// non-`TypeNs` half of a collision (`k::go::S::Inner#ns1v`, measured against a
/// one-identifier control's `k::go::S::Inner`). Read `apply_cross_namespace_tag`'s
/// "What moves" before assuming a spelling survived.
///
/// The `{{extern}}` closure does NOT have that property and must not be
/// described as if it did. It renders a segment rustc dropped
/// UNCONDITIONALLY, so **every** path that traverses an `extern` block moves —
/// including `core`/`alloc`/`std` ones (`core::ffi::c_str::strlen`,
/// `core::num::imp::libm::*`, `alloc::alloc::__rust_alloc_error_handler`). That
/// is a LOST-RECOVERY direction, so it was enumerated rather than argued:
/// across the whole tree, 1363 `core|alloc|std::…` path literals were matched
/// against the 253 item names declared in `library/{core,alloc,std}` `extern`
/// blocks; 23 share a LAST SEGMENT and only three name a genuinely foreign item.
/// All three are matched by ROOT + TAIL (`is_alloc_failure_abort_call`) or by
/// LAST SEGMENT (`trust_vcgen::ffi_vcgen`'s `is_extern_call` /
/// `extract_callee_name`), and a `ForeignMod` segment is neither a root nor a
/// tail — pinned by unit tests in both files that were watched to FAIL against a
/// planted exact-match. No `EXACT_TOTAL` entry, `has_trusted_std_root`
/// classifier or `def_path_pins` spelling names a foreign item at all.
///
/// One correction to that census, MEASURED by repo-wide grep on this tree and
/// stated because it changes what the pin buys: of those two recognizers only
/// the `ffi_vcgen` pair is LIVE (`generate/entry.rs` gates every `Call` block on
/// `is_foreign || is_extern_call` and then calls `generate_call_site_vcs`, which
/// keys on `extract_callee_name`). `is_alloc_failure_abort_call` has NO
/// production call site at all — definition, its own unit test, and this
/// sentence are its only references — so `alloc::alloc::__rust_alloc_error
/// _handler` has no live recovery lane to lose today. Its assert block pins the
/// string contract for whoever wires it up; it is not evidence of a surviving
/// discharge.
///
/// Note also that `{extern#N}` deliberately does not equal the bare keyword
/// segment `extern`, so `ffi_vcgen::is_extern_call`'s pattern-2a segment test
/// does not newly fire on every foreign path; genuine foreign imports are routed
/// by `is_foreign` (`tcx.is_foreign_item`), the authoritative signal.
/// Trust (1.101): `alloc` moved `Rc`/`Arc` (and their Weak/Unique/Inner
/// siblings) under a private `rcs` module, so definitional renderings now say
/// `alloc::rcs::arc::Arc` where every name-keyed table in the verifier stack
/// (audited destructors, foundational ADTs, drop-glue rows pinned by tests)
/// was built against the public `alloc::sync::Arc` / `alloc::rc::Rc`.
/// Canonicalize the two module prefixes back to the public re-export paths
/// at the one rendering choke point both name producers share, so identity
/// strings keep one spelling. This is a pure rename of two exact alloc
/// module prefixes; it cannot merge distinct items (no other item's
/// definitional path contains either prefix).
fn canonicalize_alloc_rcs_paths(mut rendered: String) -> String {
    if !rendered.contains("alloc::rcs::") {
        return rendered;
    }
    if rendered.contains("alloc::rcs::arc::") {
        rendered = rendered.replace("alloc::rcs::arc::", "alloc::sync::");
    }
    if rendered.contains("alloc::rcs::rc::") {
        rendered = rendered.replace("alloc::rcs::rc::", "alloc::rc::");
    }
    rendered
}

pub fn safe_def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let rendered = with_def_path_disambiguators!(with_resolve_crate_name!(with_no_visible_paths!(
        with_no_trimmed_paths!(tcx.def_path_str(def_id))
    )));
    apply_cross_namespace_tag(
        tcx,
        def_id,
        canonicalize_alloc_rcs_paths(canonicalize_rendered_lifetimes(rendered)),
    )
}

/// Trust (R150): collapse every rendered LIFETIME token to a single canonical
/// `'_`, so the two primary path producers agree on one spelling for one item.
///
/// THE BUG THIS CLOSES, measured on ny-cert (R149). The bundle names a body with
/// [`safe_def_path_str`] -> `tcx.def_path_str`, which renders the DEFINITION's
/// generic params, so `impl<'a> Parser<'a> { fn peek }` becomes
/// `ny_cert::json::Parser::<'a>::peek`. A CALL SITE names the same body with
/// [`safe_def_path_str_with_args`] -> `tcx.def_path_str_with_args`, which
/// substitutes the call's CONCRETE args, where the region is anonymous — so the
/// same item becomes `ny_cert::json::Parser::<'_>::peek`. The bridge matches
/// callees BY RENDERED NAME, so the two never met: `TRUST_BUNDLE_MEMBERS` shows
/// `Parser::<'a>::peek` KEPT as a bundle member 14 times while the caller is told
/// `body not in the lowered bundle` for `Parser::<'_>::peek`. Six ny-cert methods
/// (`peek`, `error`, `bump`, `parse_hex4`, `skip_whitespace`, `new`) lose 15
/// obligations to this, every one of them bundled, present and lowered.
///
/// SOUNDNESS — CORRECTED 2026-10-05 (SUMMARY-NAME-COLLIDE-1); the premise below
/// was FALSE as written and is kept struck so nobody re-derives it. It read:
/// "Rust has NO lifetime-based specialization and regions are erased before
/// monomorphization, so there is exactly one body per (DefId, type-args) pair
/// and two paths differing ONLY in a rendered region denote the SAME item.
/// Canonicalizing therefore cannot merge two distinct items." A region under a
/// `for<>` BINDER is part of a type's identity, not an erasable lifetime: rustc
/// accepts `impl Tr for W<for<'a> fn(&'a u8) -> &'static u8>` beside
/// `impl Tr for W<for<'a> fn(&'a u8) -> &'a u8>` (the `coherence_leak_check`
/// future-compatibility warning, rust#56105) as TWO impls with TWO bodies, and
/// both methods render `<k::W<for<'_> fn(&'_ u8) -> &'_ u8> as k::Tr>::get` here.
/// MEASURED on the stage 1 of `76a6ea45b2`: the body-derived callee summaries,
/// keyed by this rendering, handed one impl's const result to calls through the
/// other, and a false overflow-freedom row was kernel-certified
/// (`tests/ui/trust/summary_hrtb_impl_name_collision.rs`).
///
/// What remains true: for a lifetime that is NOT under a binder (`Parser::<'a>`
/// vs `Parser::<'_>`, the R149 shape) the two spellings are one item, and that is
/// the merge this exists for. What a consumer must not assume: that this
/// rendering is injective over items. A consumer that turns a rendered name into
/// a fact about ONE body has to refuse a name two items share — the body-derived
/// summary lanes do (`trust_verify::body_summary_key_collisions`). Type and const
/// arguments are untouched, so the `f::<bool>` vs `f::<i32>` discrimination that
/// [`safe_def_path_str_with_args`] exists to provide is preserved byte-for-byte.
///
/// NOT A NEW FORGERY SURFACE (false proof #14 discipline): this narrows the region
/// slot only, and anyone who could forge `<'a>` could already forge `<'_>` today.
/// The set of distinguishable non-region spellings is unchanged.
///
/// FAIL-CLOSED DIRECTION: the defect currently reports a PRESENT, PROVED body as
/// absent, which costs completeness and never soundness. Fixing it can only move
/// obligations from `unknown` toward a real verdict — and the callee body still
/// has to prove itself on its own merits once matched. (That is the R149 merge
/// only. For the binder-region pair above the merge is fail-OPEN for any
/// consumer that binds a rendered name to one body; see the correction.)
fn canonicalize_rendered_lifetimes(rendered: String) -> String {
    if !rendered.contains('\'') {
        return rendered;
    }
    let mut out = String::with_capacity(rendered.len());
    let mut chars = rendered.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\'' {
            out.push(c);
            continue;
        }
        // A lifetime token is `'` followed by either a braced sentinel the
        // renderer emits (`'{erased}`) or an identifier (`a`, `_`, `static`, `1`).
        // Consume it whole and emit the canonical form. A def path cannot contain
        // a char literal, so every `'` here is a lifetime.
        out.push('\'');
        out.push('_');
        if chars.peek() == Some(&'{') {
            for inner in chars.by_ref() {
                if inner == '}' {
                    break;
                }
            }
        } else {
            while chars.peek().is_some_and(|c| c.is_alphanumeric() || *c == '_') {
                chars.next();
            }
        }
    }
    out
}


/// The DEFINITION-side [`trust_types::CalleeIdentity`] of `def_id` — the
/// identity a CALL to this item carries when the call is the item itself rather
/// than an instantiation of it.
///
/// This is the exact counterpart of the call-site identity the extractor stamps
/// onto `Terminator::Call::callee_identity`, computed by the SAME function
/// ([`convert::callee_identity_for`]) over the item's own
/// `GenericArgs::identity_for_item`. Two consequences, both deliberate:
///
/// * **The `'a`/`'_` desync closes.** For an item whose only generic parameters
///   are LIFETIMES — `impl<'a> Parser<'a> { fn peek(&self) }`, the measured R43
///   blocker — the identity args are `['a]` and a call site's are `['_]`. Both
///   erase to `[ReErased]`, so both sides produce the SAME digest and the same
///   `DefId` halves. The two keys meet because they denote the same code, not
///   because a string was rewritten.
/// * **A type/const-generic item gets `None`, and must.** Its identity args
///   mention a `ty::Param`, which `callee_identity_for` refuses. So a fact
///   registered about the ONE pre-monomorphization body verified for a generic
///   item can never be transferred to a concrete call `f::<u32>` by this route —
///   "the generic body verified" does not imply "every instantiation is
///   panic-free", and that distinction is exactly what the argument-free
///   `safe_def_path_str` key lost.
///
/// Callers must treat `None` as "no identity-keyed decision is available",
/// NEVER as a licence to compare rendered paths instead.
pub fn item_identity(tcx: TyCtxt<'_>, def_id: DefId) -> Option<trust_types::CalleeIdentity> {
    convert::callee_identity_for(
        tcx,
        def_id,
        rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id),
    )
}

/// The definition-side [`trust_types::CalleeIdentity`] of one fully resolved
/// instantiation.
///
/// This is the instantiated counterpart of [`item_identity`].  It is exposed
/// for compiler-owned provenance ledgers that already hold the exact
/// [`rustc_middle::ty::Instance`] whose MIR they instantiated.  The same
/// fail-closed rules as the call-site extractor apply: type/const parameters,
/// inference variables, and placeholders return `None`; regions alone are
/// erased before the substitution digest is minted.
///
/// Consumers must compare the result to a call's extracted
/// `Terminator::{Call,TailCall}::callee_identity`; rendered function names are
/// diagnostic labels and are not a fallback identity.
pub fn instance_identity<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> Option<trust_types::CalleeIdentity> {
    convert::callee_identity_for(tcx, def_id, args)
}

/// Like [`safe_def_path_str`] but renders the path with its CONCRETE
/// monomorphized generic arguments (`std::vec::Vec::<[u8; 1099511627776]>::with_capacity`
/// rather than the generic `Vec::<T>::with_capacity`). Used for bulk-allocation
/// sink callees so the element type — and hence `size_of::<T>()` — is recoverable
/// downstream for the capacity-overflow (`count * size_of::<T>() < isize::MAX`)
/// obligation, which the count-only path cannot establish for a multi-byte element
/// (SOUNDNESS, hunt-11: a `Vec::<[u8; 1<<40]>::with_capacity(n)` capacity overflow
/// was reported proved — and kernel-certified — because `T` was erased to the
/// generic param here).
///
/// Discrimination (NOT injectivity): see [`safe_def_path_str`]. The FLAG reaches
/// the nested types too (`args` and an impl's `Self`/trait ref all print through
/// the same `print_path_with_simple`) — but read "the flag" literally: the
/// cross-namespace TAG is not a flag, it is a suffix computed from this
/// `def_id`'s own chain by [`apply_cross_namespace_tag`], and it does NOT reach
/// the nested types (§RESIDUAL 7c there, with two measured witnesses). The flag
/// is what separates
/// `<krate::f::S as core::fmt::Write>::write_fmt` from its sibling — there the
/// ambiguity is in the SELF TYPE, not in the callee's own segments. The self type
/// is also where the residual lives: this function renders a CALL's key from the
/// caller's `args`, and a generic `args` vector renders exactly like the
/// DEFINITION path of a generic body (`direct_call_def_path`, residual 1). That
/// was a MEASURED false proof through `func_operand_name`, which now tags such a
/// trait call when it equals a local definition key (GENERIC-CALL-KEY-ALIAS-1).
/// This function does not tag: a caller that names a CALL with it directly must
/// not match the result against a body's key.
pub fn safe_def_path_str_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> String {
    let rendered = with_def_path_disambiguators!(with_resolve_crate_name!(with_no_visible_paths!(
        with_no_trimmed_paths!(tcx.def_path_str_with_args(def_id, args))
    )));
    // R150: the SAME canonicalization the definition-side producer applies, so one
    // item has one spelling on both sides. See `canonicalize_rendered_lifetimes`.
    apply_cross_namespace_tag(
        tcx,
        def_id,
        canonicalize_alloc_rcs_paths(canonicalize_rendered_lifetimes(rendered)),
    )
}

/// Trust (§RESIDUAL 7 — the cross-NAMESPACE collision): append the namespace tag,
/// if this `def_id`'s path has a segment that is ambiguous across namespaces.
///
/// # The defect, MEASURED
///
/// rustc's `DisambiguatedDefPathData` disambiguator counts siblings per `(parent,
/// DefPathData)`, and `DefPathData::TypeNs(sym)` / `ValueNs(sym)` are DIFFERENT
/// VARIANTS. A `fn S` and a `struct S` under one parent are therefore both `#0`
/// and both render `S`, which no closure inside `print_path_with_simple` can
/// separate — the disambiguator it prints is already the right one for the
/// namespace it was counted in.
///
/// On pristine main `a27d636271`, `probe/nsclash.rs` (a fn-block `fn S(v: u32)`
/// containing `fn m`, plus a separate block `struct S; impl S { fn m }`, both
/// called from one `go`) produced TWO distinct bundled bodies whose bundle roots
/// both render `t_nsclash::go::S::m` — the two `-Ztrust-dump=native-bundle`
/// modules carry `vc:t_nsclash__go__S__m:trust_mc_default_function:0` and
/// `vc:t_nsclash__go__S__m:arithmetic_safety:0` respectively. The measured
/// consumer-level differential against the one-identifier control
/// (`struct S2`) is in `go`'s OWN bundle: control renders four members
/// `[go, S, m, m]` and ONE obligation, the clash renders three `[go, m, m]` —
/// the `fn S` member is GONE — and TWO obligations, the extra one being
/// `vc:t_nsclash__go:assertion:panic-freedom:0`. In that shape the alias costs
/// credit rather than granting it, which is a LOST RECOVERY and a defect in its
/// own right; the fail-OPEN direction of this same one-string-two-`DefId`s key is
/// what the three witnesses on `convert::direct_call_def_path` were.
///
/// # Why the tag is here and not inside `print_path_with_simple`
///
/// The printer's segment hook is handed a `DisambiguatedDefPathData` and nothing
/// else: no `DefId`, no parent, no sibling set. The objection recorded on
/// `direct_call_def_path` — that separating the namespaces means tagging EVERY
/// named segment, modules included, so every path in the identity space moves —
/// is correct FOR THAT HOOK, and it is the reason this was left open. It is
/// answered by moving the decision one frame out, to the seam's entry points
/// (the two functions that turn the flag on), where the `DefId` is in hand and a
/// sibling index can be consulted. Only a segment with an actual cross-namespace
/// sibling is tagged.
///
/// # CORRECTION, 2026-08-21 — this tag has been LIVE since `12f3b32af9`
///
/// It landed on 2026-08-18 in `9440395b41`, was reverted with the assumption
/// census in `16be43eca1`, and came back on 2026-08-19 12:55 in `12f3b32af9`,
/// whose message is entirely about the census — the namespace half rode along
/// unmentioned. Nothing was re-measured, so three neighbouring claims went on
/// saying OPEN: this seam's own paragraph above, `direct_call_def_path`
/// §RESIDUAL 7, and `reports/soundness-findings-status-2026-08-19.md`, written
/// two hours after the tag was restored. Re-measured 2026-08-21 on the STAGE2
/// `trustc` built from `ddb545d35b` (every number in this comment is from that
/// binary unless it says otherwise), the shape §RESIDUAL 7 documents now renders
/// FOUR bodies under FOUR paths where it rendered four under three, and its
/// native-bundle keys separate:
/// `vc:h0_nsclash__go__S__m_x23ns1v:trust_mc_default_function:0` against
/// `vc:nsclash__go__S__m:arithmetic_safety:0`. Its consumer differential is
/// gone: the clash and its one-identifier control both report `0 proved,
/// 1 failed … out of 1 obligation(s)`.
/// Pinned by `tests/ui/trust/cross_namespace_key_alias_stays_closed.rs`, watched
/// red by renaming the `struct S` to `S2`.
///
/// # What moves — MEASURED, not argued
///
/// The tag is a SUFFIX (`#ns<depth><ns-letter>`, `.`-separated for more than one
/// segment), so ROOT-anchored classifiers are untouched; `#` cannot occur in a
/// Rust path, exactly as for the `{extern#N}` segment and the `@`-stamp.
///
/// The `letter == 't'` skip in `cross_namespace_tag` buys exactly one thing and
/// it must not be over-read: of the colliding PAIR, the `TypeNs` half's OWN
/// segment is never marked. It does NOT keep `TypeNs` spellings in general,
/// because the tag is a suffix over the WHOLE `DefPath` CHAIN — so any LOCAL
/// item, in ANY namespace, that sits UNDER a marked ancestor moves with it.
/// MEASURED, same crate name `k`, one identifier apart (`struct S` renamed
/// `S2`), a `mod M` with an ADT, a trait, a trait impl and a fn nested inside a
/// `fn S` that collides with a sibling `struct S`:
///
/// ```text
/// clash                                          control
/// k::go::S::M::Ad#ns1v                           k::go::S::M::Ad
/// k::go::S::M::mf#ns1v                           k::go::S::M::mf
/// <k::go::S::M::Ad as k::go::S::M::Tr>::t#ns1v   <k::go::S::M::Ad as k::go::S::M::Tr>::t
/// k::go::S::Inner#ns1v (a nested ADT)            k::go::S::Inner
/// ```
///
/// An earlier revision of this comment claimed those spellings were
/// byte-identical. They are not, and the claim was also load-bearing for the
/// wrong reason: what actually keeps every `core::`/`alloc::`/`std::` spelling
/// byte-identical is the `!def_id.is_local()` early return, and NOTHING else.
/// MEASURED on the same clash/control pair, which allocates a `Vec<u8>` so the
/// foreign surface is non-empty: all ten rendered `core::`/`alloc::` strings —
/// `alloc::vec::Vec::<u8>::with_capacity::<__trust_elem_bytes@1>`,
/// `core::hint::black_box::<&alloc::vec::Vec<u8>>`, `alloc::alloc::Global`,
/// `core::ptr::non_null::NonNull` and the rest — are byte-identical across the
/// two. Note the corollary for the other half of the pair: descendants of the
/// `TypeNs` half do NOT move (a `pub mod S` beside a `pub fn S` renders its
/// child `nsdep::S::inner` untagged), because the mod segment is the one the
/// `'t'` skip declines to mark.
///
/// Sampled on the stage2 `trustc` from `ddb545d35b`, every body dumped by
/// `-Ztrust-dump=mir`, one source file at a time:
///
/// | population | files | bodies | distinct paths | tagged paths |
/// |---|---|---|---|---|
/// | A — all of `tests/ui/trust`, top level + all six subdirs | 298 | 750 | 747 | **4 — all in this change's own 3 fixtures** |
/// | B — rustc's `tests/ui/{generics,impl-trait,imports,macros,modules,structs,traits}` | 2876 | — | — | **17** |
///
/// **Population A moved by ZERO paths outside this change's own fixtures**, and by
/// zero STRINGS: the only `#ns` occurrences `grep -r` finds anywhere in the dumps
/// are the five in `cross_namespace_key_alias_stays_closed`,
/// `…does_not_fire_on_a_macro_shadow` and `…does_not_fire_on_an_assoc_type_shadow`
/// — nothing in any other fixture's def path, callee key, type name or `Self`
/// type. Everything Trust graded before this change is untouched, so the
/// `EXACT_TOTAL` lost-recovery direction is unreachable there.
///
/// The BODY and DISTINCT-PATH counts are a property of the harness, not of the
/// tag, and are left out of B for that reason: they move with the dump directory
/// layout, with which fixtures a run manages to compile, and — in B, which runs
/// each file under a 30-second timeout — with machine load. Two sweeps of A
/// reported 750/747 and 848/851; two of B reported 3624/3612 and 3411/3400. What
/// REPRODUCES is the TAG SET, and that is what this table is for: A's "none
/// outside the new fixtures", and B's 17 with the enumeration below, of which
/// `tests/ui/imports` was re-swept here (265 files) and returned exactly its two,
/// `imports::c::test#ns1v` and `imports::c::test::f#ns2v`.
///
/// Across both populations EVERY tag letter observed was `v`: no `#ns…t`,
/// `#ns…m` or `#ns…l` occurs anywhere. That absence is the load-bearing
/// measurement for the `MacroNs` narrowing below. Read it as an absence of
/// `t`/`m`/`l` MARKS, NOT as an absence of movement in the `TypeNs` namespace —
/// the four `#ns1v` paths above are all `TypeNs`-rooted and every one of them
/// carries a `v` mark inherited from an ancestor.
///
/// Both directions matter here — a spelling change that stops matching an
/// `EXACT_TOTAL` summary entry LOSES a sound recovery. Every
/// `EXACT_TOTAL`/`def_path_pins`/`has_trusted_std_root` spelling names a
/// `core`/`alloc`/`std` item, all of which are FOREIGN to any crate under
/// verification and so cannot be tagged at all — by the `is_local` return above,
/// measured, not by the `'t'` skip.
///
/// # RESIDUAL 7a — the tag STOPS AT THE CRATE BOUNDARY, and that is asymmetric
///
/// The sentence that used to close the paragraph above — "the definition path
/// and the call key are rendered from the same `def_id` through these same two
/// functions, so they move together or not at all" — is MEASURED FALSE. They
/// move together only WITHIN one compilation. `cross_namespace_tag` returns
/// early on `!def_id.is_local()`, so a tagged definition is unreachable by name
/// from downstream: compiling `pub mod S { … } pub fn S(..)` renders the
/// function `nsdep::S#ns0v`, and compiling a crate that calls it renders the
/// SAME `DefId` as `nsdep::S`. One `DefId`, two keys, split by the crate
/// boundary.
///
/// What that costs is bounded by measurement, not by argument: within any single
/// compilation the whole identity space is rendered by the same crate, so the
/// bundled body, the callee key and the contract-summary key agree, and no
/// differential was found through the routes tried. Two of those routes are
/// re-measured here — the downstream bundle carries NO foreign body (see 7b), and
/// the two-crate probe above — and one is inherited without re-measurement: an
/// `ensures`-bearing colliding callee consumed cross-crate was reported identical
/// to its control, on a lane that is dark anyway
/// (`modular_callee_postcondition_reuse.rs` is `//@ ignore-test`, verified).
/// Stated as a gap because the serialized-artifact consumers are where it would
/// bite. An ordinary `trait T { type A; fn A(); }` walks into this gap for free;
/// see the over-decline recorded on `def_path_data_namespace`.
///
/// # RESIDUAL 7b — a FOREIGN cross-namespace collision is not detected
///
/// The index is built from `tcx.hir_crate_items(())`, which enumerates the LOCAL
/// crate only; there is no cross-crate query that enumerates the children of an
/// arbitrary foreign parent (`module_children` covers modules, not the
/// block-scoped items inside a foreign body that reach us through inlined MIR).
/// A foreign `def_id` is therefore never tagged. This is stated as a gap, not
/// argued away, and it is NOT failed closed: a renderer has no fail-closed
/// channel — it must return a string — and turning every foreign path into a
/// refusal is a lost recovery with no measured exploit behind it. Probed, and
/// NOT reached by the obvious route: the §RESIDUAL 7 shape moved into a generic
/// `#[inline]` body in a dependency and instantiated downstream put NO foreign
/// body in the consumer's bundle, so the alias had nothing to alias.
///
/// # RESIDUAL 7c — the tag covers `def_id`'s OWN chain, never a NESTED type
///
/// `cross_namespace_tag` walks the chain of the `def_id` it is handed and appends
/// one suffix to the finished string. Types rendered INSIDE a path — the generic
/// `args`, an impl's `Self` type, a trait ref — arrive through `def_path_str
/// _with_args`'s own printer and are never passed to this function, so they are
/// never tagged. [`safe_def_path_str_with_args`]'s doc says "the flag reaches the
/// nested types too"; that is true of `with_def_path_disambiguators!`, which is a
/// printer flag, and FALSE of this tag, which is not.
///
/// Two consequences, both MEASURED on `ddb545d35b`'s stage2 `trustc`, crate name
/// `k` throughout.
///
/// 1. **One type gets TWO spellings in ONE bundle.** With `fn S`/`struct S`
///    colliding under `go` and a `struct Inner` plus a generic `fn take<T>`
///    inside `fn S`, one dump carries both
///    `k::go::S::Inner#ns1v` (rendered standalone, as a type name) and
///    `k::go::S::take::<k::go::S::Inner>#ns1v` (the call key) — the SAME `Inner`,
///    spelled with the tag in one place and without it in the other. Any consumer
///    that matches an args-embedded type name against a standalone type name must
///    not assume the two spellings agree.
///
/// 2. **Two DISTINCT local types collapse to ONE args spelling.** `fn S(..) {
///    struct Inner([u8; 1 << 40]); }` beside `mod S { pub struct Inner(pub u8); }`
///    under one `go` — the `fn S`/`mod S` pair IS in the collision index and the
///    `fn S` body's own path duly renders `k::go::S#ns1v` — yet the two `Inner`s
///    are BOTH rendered `k::go::S::Inner` inside args. Measured, the two
///    `Vec::with_capacity` calls come out as
///    `alloc::vec::Vec::<k::go::S::Inner>::with_capacity::<__trust_elem_bytes@1>`
///    and `…::<__trust_elem_bytes@1099511627776>`: DIFFERENT keys, but the
///    difference is entirely `direct_call_def_path`'s separate
///    `__trust_elem_bytes@N` stamp — the hunt-11 capacity lane survives on THAT
///    and not on this tag. Strip the stamp and the two keys are equal. In the
///    same dump the two `black_box` calls, which carry no stamp, DO collapse:
///    `core::hint::black_box::<&alloc::vec::Vec<k::go::S::Inner>>` occurs twice,
///    once per element type. I did NOT drive a false proof through either; this is
///    recorded as a live alias with a measured witness, not as a safe class.
fn apply_cross_namespace_tag(tcx: TyCtxt<'_>, def_id: DefId, rendered: String) -> String {
    match cross_namespace_tag(tcx, def_id) {
        Some(tag) => rendered + &tag,
        None => rendered,
    }
}

/// The namespace letter this `DefPathData` variant contributes to the index, and
/// the symbol it is keyed by. `Impl`/`Ctor`/`Closure`/... carry no user-chosen
/// name in a namespace and cannot participate.
///
/// # Why `MacroNs` and `LifetimeNs` are NOT here — an OVER-DECLINE, measured
///
/// They were, and it moved honest paths. A name only belongs in this index if
/// this seam can RENDER it, because the index exists to decide whether two
/// renderings collide; a namespace nothing renders into can only ever move its
/// partner. Both absences are measured, not reasoned:
///
/// * `MacroNs`. A `macro_rules!` has no MIR body and is never a callee, a type
///   or a `Self`, so it never reaches a renderer — MEASURED as an ABSENCE with
///   teeth: in `tests/ui/macros/meta-variable-misuse.rs` the macros `a`/`b`/`c`
///   collide with fns `a`/`b`/`c`, and the fns came back
///   `meta_variable_misuse::{a,b,c}#ns0v` while the macros never appeared at
///   all; across both sampled populations not one `#ns…m` was rendered. So the entry
///   bought nothing and cost this: a crate with `#[macro_export] macro_rules!
///   increment` beside `pub fn increment` — the ordinary Rust idiom, no
///   ambiguity anywhere in the identity space — rendered its function
///   `macro_crate_use::increment#ns0v`.
///
///   ELEVEN of the SEVENTEEN tags on population B are this shape and nothing
///   else — `cfg_expr::{BAR,baz,quux}`, `cfg_select_expr::{BAR,baz,quux}`,
///   `meta_variable_misuse::{a,b,c}`, `macro_crate_use::increment`,
///   `macro_crate_nonterminal::increment`. The remaining SIX are genuine
///   `TypeNs`/`ValueNs` pairs and MUST keep their tags:
///   `imports::c::test` (`mod test` + `fn test`), `imports::c::test::f`
///   (`pub mod f` + `pub fn f`), `special_module_name_ignore::main`
///   (`mod main;` + `fn main`), `issue_2936::cbar` (`struct cbar` + `fn cbar`),
///   `generic_impl_method_params_2311::foo` (`struct foo<A>` + `fn foo<A>`),
///   `issue_114682_2_extern::d::max` (`pub fn max` + `pub(crate) mod max`).
///   Nearly two thirds of every tag this seam emitted was noise, and each one put
///   an exported function into §RESIDUAL 7a's asymmetric class for nothing.
/// * `LifetimeNs`. A lifetime's `Symbol` carries its leading `'`, so it cannot
///   equal a type or value symbol at all — MEASURED as a falsify-once PAIR, same
///   shape, same compiler, the partner item the only difference:
///   `fn f<'a>(r: &'a u32) { fn a(..) {} … }` puts `'a` and `a` under ONE parent
///   and renders `k::f::a` UNTAGGED, while `fn f(..) { mod a {…} fn a(..) {} … }`
///   — a genuine `TypeNs`/`ValueNs` pair in the same position — renders
///   `k::f::a#ns1v`. The `l` entry could therefore never have fired on the first
///   shape, and removing it cannot suppress the second.
///
/// NOT BUILT: this narrowing and the `DefKind::ExternCrate` filter in
/// `local_cross_namespace_collisions` are the two edits in this change that a
/// rebuilt `trustc` has not executed (`x.py` is not available to the author). What
/// they have instead, and what they do not have, stated exactly:
///
/// * The selection logic above, the `def_kind` filter in
///   `local_cross_namespace_collisions` and the mark loop in `cross_namespace_tag`
///   were extracted into a standalone program with 9 cases, and EACH REMOVAL WAS
///   WATCHED TO FAIL FIRST, on its own `cfg`. With the pre-change letter set
///   `['t','v','m','l']` the macro-shadow case asserts `[(0,'v')]` where `[]` is
///   required — exit 101. With `['t','v']` but no `def_kind` filter, the
///   extern-crate-shadow case fails the same way — exit 101. With both, all 9 pass
///   — exit 0. The cases cover the real `TypeNs`/`ValueNs` pair, the macro shadow,
///   a three-way `m`+`t`+`v` (a macro must not be able to SUPPRESS a real tag), a
///   lifetime shadow, the extern-crate shadow, an extern crate beside a real pair
///   (it must not suppress that tag either), different parents, mark inheritance
///   by a descendant, and `Impl`/`Ctor`/`Closure` non-participation.
/// * Both narrowings are strictly subtractive — they can only remove entries from
///   the collision index, hence only remove tags, never add one — and the graded
///   corpus contains no tag to remove: 298 `tests/ui/trust` fixtures swept on the
///   stage2 `trustc` from `ddb545d35b`, 750 dumped bodies, 747 distinct def paths,
///   and the only `#ns` occurrences anywhere in the dumps are the four paths in the
///   three fixtures this change adds. One of those four,
///   `…_macro_shadow::increment#ns0v`, is precisely the tag the `MacroNs` removal
///   deletes, which is why that fixture shipped `//@ ignore-test`. So neither
///   narrowing can disturb the suite.
/// * RUN in a compiler 2026-09-27 (stage1 at `49d76d46097`), five weeks after this
///   landed unbuilt; all three probes on `apply_cross_namespace_tag` hold:
///   `macro_rules! foo` beside `pub fn foo` renders `k::foo`; `#![no_std] extern
///   crate alloc;` beside `pub fn alloc` renders `k::alloc` (was `k::alloc#ns0v`);
///   and `mod S` beside `fn S` STILL renders `k::S#ns0v`, so it did not over-reach.
///   `tests/ui/trust/cross_namespace_tag_does_not_fire_on_a_macro_shadow.rs` is the
///   first as a fixture, now live and green; the third is
///   `cross_namespace_key_alias_stays_closed.rs`, which is live and green.
///
/// # `TypeNs` names this seam cannot render — ONE FIXED, TWO RECORDED
///
/// The rule above ("a name belongs in this index only if this seam can RENDER
/// it") is not satisfied by every `TypeNs` name, and the ones that fail it are
/// reached by ordinary Rust idioms, not by contrived collisions.
/// `rustc_hir/src/def.rs` maps `DefKind::ExternCrate`, `DefKind::TyAlias` and
/// `DefKind::AssocTy` into the same `DefPathData::TypeNs` arm as `Mod`, so all
/// three enter this index and tag their `ValueNs` partner. Three were PROBED and
/// are listed below; that is what was probed, NOT a proof of exhaustiveness over
/// that arm.
///
/// * **`ExternCrate` — FIXED**, in `local_cross_namespace_collisions`, because it
///   has exactly the premise `MacroNs` has and the premise is measured: with
///   `extern crate alloc as A;` the dumps render `alloc::vec::Vec`, never
///   `A::vec::Vec`, and an extern-crate binding has no MIR body and is never a
///   callee, a type, a `Self` or a rendered path prefix — so its entry could only
///   ever move its partner. Falsify-once pair on `ddb545d35b`'s stage2, one
///   identifier apart: `#![no_std] extern crate alloc; pub fn alloc(v: u32) -> u32`
///   rendered `k::alloc#ns0v`, while `extern crate alloc as ax;` with the
///   byte-identical function renders `k::alloc`. Two-crate consequence, straight
///   into §RESIDUAL 7a: the defining crate rendered `ecdep::alloc#ns0v` and a
///   consumer of it rendered `ecdep::alloc` — one `DefId`, two keys, on an EXPORTED
///   function reached by ordinary `#![no_std]` Rust.
/// * **`TyAlias` — RECORDED, not fixed.** `pub type S = u32; pub fn S(v: S) -> S`
///   renders `k::S#ns0v` against the one-identifier control `pub type Q = u32;`,
///   which renders `k::S`. It is left standing for the same reason as `AssocTy`
///   below and no other: a type alias IS a type, so the non-renderability premise
///   that licences the `ExternCrate` and `MacroNs` removals is NOT established for
///   it.
/// * **`AssocTy` — RECORDED, not fixed**, with its witness:
///
/// An associated TYPE and an associated FN with the same name are siblings under
/// the SAME parent — the `impl` — so they enter the index as a `t`/`v` pair and
/// the METHOD is tagged. MEASURED on `ddb545d35b`'s stage2 `trustc`, same crate
/// name `k`, one identifier apart (`type A` renamed `type B`):
///
/// ```text
/// pub trait T { type A; fn A(v: u32) -> u32; }   ->  <k::X as k::T>::A#ns1v
/// pub trait T { type B; fn A(v: u32) -> u32; }   ->  <k::X as k::T>::A
/// ```
///
/// That is a spelling move on an honest path, and on an EXPORTED one: it drops
/// the method straight into §RESIDUAL 7a. MEASURED with a two-crate probe —
/// compiling the dependency renders `<assocdep::X as assocdep::T>::A#ns1v`,
/// while compiling a consumer that calls it renders the SAME `DefId` as
/// `<assocdep::X as assocdep::T>::A`. One `DefId`, two keys, and no source-level
/// ambiguity anywhere to justify either.
///
/// WHY IT IS NOT FIXED HERE, stated rather than glossed. The fix is mechanically
/// available and the `ExternCrate` line above proves it — the loop has
/// `tcx.def_kind` in hand, so `DefKind::AssocTy` is one more `matches!` arm — but
/// it needs a premise this author cannot establish: that no associated type ever
/// reaches this seam. `MacroNs` and `ExternCrate` have that premise structurally
/// and measurably (no MIR body, not a type, never rendered — and for
/// `extern crate alloc as A;` the seam was watched rendering `alloc::…`, never
/// `A::…`); an associated type IS a type, so the argument does not transfer, and the
/// evidence I have is one probe — a `P::Assoc`/`<X as Tr>::Assoc` signature pair
/// that rustc normalized to `u32` and never rendered — against ~100 call sites
/// of [`safe_def_path_str`]/[`safe_def_path_str_with_args`] across
/// `trust-mir-extract`, `trust-thir-lower` and `rustc_mir_transform`, several of
/// which take their `DefId` from an attribute or allocation scan rather than
/// from a body. Dropping the entry on that evidence would create the alias in
/// the fail-OPEN direction (both halves rendering `<X as T>::A`) to remove a
/// lost recovery, which is the wrong trade to make blind. So it is recorded with
/// its witness and left standing.
///
/// Pinned by `tests/ui/trust/cross_namespace_tag_does_not_fire_on_an_assoc_type
/// _shadow.rs`, which is `//@ ignore-test` and RED ON PURPOSE: it asserts the
/// spelling this seam OUGHT to produce. Un-ignore it in the same commit that
/// drops `DefKind::AssocTy` from the index, and not before — and do not read that
/// commit as closing the class: `TyAlias` would still be in the index, and these
/// three names are what was probed, not an enumeration of `def.rs`'s `TypeNs` arm.
fn def_path_data_namespace(data: rustc_hir::definitions::DefPathData) -> Option<(Symbol, char)> {
    use rustc_hir::definitions::DefPathData;
    match data {
        DefPathData::TypeNs(name) => Some((name, 't')),
        DefPathData::ValueNs(name) => Some((name, 'v')),
        _ => None,
    }
}

/// Every `(parent, symbol)` in the LOCAL crate that is declared in more than one
/// namespace. Keyed by raw `u32`s so the cache needs no rustc lifetime.
type CrossNamespaceIndex = Arc<FxHashSet<(u32, u32)>>;

static CROSS_NAMESPACE_INDEX: std::sync::Mutex<Option<(u64, Option<CrossNamespaceIndex>)>> =
    std::sync::Mutex::new(None);

thread_local! {
    static THREAD_CROSS_NAMESPACE_INDEX: std::cell::RefCell<
        Option<(u64, Option<CrossNamespaceIndex>)>,
    > = const { std::cell::RefCell::new(None) };
}

/// Build (once per compiled crate) the set of `(parent DefIndex, Symbol)` pairs
/// that the local crate declares in two or more namespaces, or `None` when the
/// local crate has no cross-namespace collisions.
///
/// Cached against the local `StableCrateId` rather than a bare `OnceLock` so a
/// process that drives `rustc_interface` more than once cannot read the previous
/// crate's index, with a thread-local fast path so worker threads avoid locking
/// `CROSS_NAMESPACE_INDEX` or cloning an empty `Arc` on every `safe_def_path_str`.
fn local_cross_namespace_collisions(tcx: TyCtxt<'_>) -> Option<CrossNamespaceIndex> {
    let stable_crate_id = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    if let Some(hit) = THREAD_CROSS_NAMESPACE_INDEX.with(|cell| {
        let borrow = cell.borrow();
        match borrow.as_ref() {
            Some((cached_id, index)) if *cached_id == stable_crate_id => Some(index.clone()),
            _ => None,
        }
    }) {
        return hit;
    }
    // The lock is NEVER held across the `hir_crate_items` query below. Holding it
    // would deadlock a `std::sync::Mutex` (not reentrant) if that query — or any
    // diagnostic it emits — rendered a path through this seam. A lost race only
    // costs a second identical computation.
    {
        let slot = CROSS_NAMESPACE_INDEX.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((cached_id, index)) = slot.as_ref() {
            if *cached_id == stable_crate_id {
                let cloned = index.clone();
                THREAD_CROSS_NAMESPACE_INDEX.with(|cell| {
                    *cell.borrow_mut() = Some((stable_crate_id, cloned.clone()));
                });
                return cloned;
            }
        }
    }
    let defs = tcx.hir_crate_items(()).definitions();
    let mut namespaces: FxHashMap<(u32, u32), u8> =
        FxHashMap::with_capacity_and_hasher(defs.size_hint().0, Default::default());
    for local in defs {
        let key = tcx.def_key(local.to_def_id());
        let Some(parent) = key.parent else { continue };
        let Some((name, letter)) = def_path_data_namespace(key.disambiguated_data.data) else {
            continue;
        };
        // `DefKind::ExternCrate` is a `DefPathData::TypeNs` (`rustc_hir/src/def.rs`,
        // same arm as `Mod` and `TyAlias`), but an extern-crate BINDING is never
        // rendered by this seam — with `extern crate alloc as A;` the dumps carry
        // `alloc::vec::Vec`, never `A::vec::Vec` (measured) — so an entry for it can
        // only ever move its ValueNs partner. That is the `MacroNs` premise exactly,
        // and `#![no_std] extern crate alloc; pub fn alloc(..)` walks into it from
        // ordinary Rust: it rendered `k::alloc#ns0v` against the one-identifier
        // control's `k::alloc`, and cross-crate `ecdep::alloc#ns0v` at the definition
        // against `ecdep::alloc` at the consumer (§RESIDUAL 7a) — one `DefId`, two
        // keys, on an EXPORTED function nothing in the source made ambiguous.
        if matches!(tcx.def_kind(local.to_def_id()), DefKind::ExternCrate) {
            continue;
        }
        // `unwrap_or` would fold an unlisted letter onto `t`'s bit and hide it
        // from `count_ones`; every letter `def_path_data_namespace` can return
        // must be listed here, so an unlisted one is a bug, not a default.
        let shift = match letter {
            't' => 0u8,
            'v' => 1u8,
            _ => {
                debug_assert!(false, "namespace letter {letter:?} has no index bit");
                continue;
            }
        };
        *namespaces.entry((parent.as_u32(), name.as_u32())).or_default() |= 1u8 << shift;
    }
    let mut index = FxHashSet::default();
    #[allow(rustc::potential_query_instability)]
    for (key, mask) in namespaces {
        if mask.count_ones() > 1 {
            index.insert(key);
        }
    }
    let index: Option<CrossNamespaceIndex> = (!index.is_empty()).then(|| Arc::new(index));
    {
        let mut slot = CROSS_NAMESPACE_INDEX.lock().unwrap_or_else(|e| e.into_inner());
        *slot = Some((stable_crate_id, index.clone()));
    }
    THREAD_CROSS_NAMESPACE_INDEX.with(|cell| {
        *cell.borrow_mut() = Some((stable_crate_id, index.clone()));
    });
    index
}

/// The tag for one `def_id`, or `None` when no segment of its path is ambiguous
/// across namespaces. See [`apply_cross_namespace_tag`] for the argument.
fn cross_namespace_tag(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    // Foreign paths are the documented residual, and skipping them here is also
    // what keeps every `core::`/`alloc::`/`std::` spelling byte-identical.
    if !def_id.is_local() {
        return None;
    }
    let index = local_cross_namespace_collisions(tcx)?;
    // Walk to the crate root so the mark can name a segment by DEPTH; a middle
    // segment is where the measured collision sits (`go::S::m`), so tagging the
    // last segment alone would not separate the two paths.
    let mut hits: Vec<(usize, char)> = Vec::new();
    let mut total_depth = 0usize;
    let mut current = def_id;
    loop {
        let key = tcx.def_key(current);
        let Some(parent) = key.parent else {
            break;
        };
        if let Some((name, letter)) = def_path_data_namespace(key.disambiguated_data.data) {
            if letter != 't' && index.contains(&(parent.as_u32(), name.as_u32())) {
                hits.push((total_depth, letter));
            }
        }
        total_depth += 1;
        current = DefId { krate: def_id.krate, index: parent };
    }
    if hits.is_empty() {
        return None;
    }
    use std::fmt::Write;
    let mut tag = String::with_capacity(3 + hits.len() * 4);
    tag.push_str("#ns");
    for (i, &(rev_idx, letter)) in hits.iter().rev().enumerate() {
        if i > 0 {
            tag.push('.');
        }
        let depth = total_depth - 1 - rev_idx;
        let _ = write!(tag, "{depth}{letter}");
    }
    Some(tag)
}

/// Authenticate a crate using the extractor's existing loader-residency and
/// sysroot-building-invocation policy. This authenticates the CRATE only;
/// callers must separately check the intended item identity (for example a
/// compiler lang item). Lang/diagnostic-item attributes alone are not authority.
pub fn is_real_sysroot_crate(tcx: TyCtxt<'_>, krate: rustc_span::def_id::CrateNum) -> bool {
    convert::is_real_sysroot_crate(tcx, krate)
}

/// [`safe_def_path_str`] plus the SYSROOT-IMPERSONATION stamp — the renderer for
/// every TYPE name the extractor emits.
///
/// A `Ty::Adt`/`Ty::Datatype`/`AggregateKind::Adt` name is authenticated
/// downstream by its printed root alone
/// (`trust_vcgen::generate::alloc_vcs::ty_is_authenticated_std_iterator`), so a
/// crate built `--crate-name std` used to hand out `std::vec::Endless` and be
/// believed. `convert::sysroot_authenticated_path` carries the argument for why
/// this is rule 2 only, why an honest graph renders byte-for-byte what it
/// rendered before, and what the anchors still do NOT authenticate (residual R2).
///
/// EVERY site that renders a name into the emitted IR must use this, including
/// the by-name back-edge/cut references, or a stamped definition and an unstamped
/// reference to it stop matching and the recursion guards lose their key.
pub fn sysroot_authenticated_def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    convert::sysroot_authenticated_path(tcx, def_id.krate, safe_def_path_str(tcx, def_id))
}

/// [`safe_def_path_str_with_args`] plus the SYSROOT-IMPERSONATION stamp. See
/// [`sysroot_authenticated_def_path_str`].
pub fn sysroot_authenticated_def_path_str_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> String {
    convert::sysroot_authenticated_path(
        tcx,
        def_id.krate,
        safe_def_path_str_with_args(tcx, def_id, args),
    )
}

/// Trust (policy B as ruled, 2026-09-14): is `def_id` defined in one of THIS
/// compiler's own sysroot crates (`core`/`alloc`/`std`), authenticated the
/// un-forgeable way — by the loaded artifact's residence in the compiler's own
/// target library directory, never by the crate's NAME. A dependency compiled
/// `--crate-name std` answers `false` here; see `convert::is_real_sysroot_crate`
/// for the impersonation history this rules out.
///
/// `pub` for the verifier driver's completeness-gap tolerance: an absent callee
/// whose panic has vanilla Rust semantics (so the ruling says "report, do not
/// fail") is one that BOTH lives here AND takes only foundational type
/// arguments; this answers the first half.
pub fn def_is_in_real_sysroot_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    convert::is_real_sysroot_crate(tcx, def_id.krate)
}

/// Trust (X1, 2026-09-23): is `def_id` defined in a crate this compiler loaded
/// from its OWN target library directory — `core`/`alloc`/`std` AND their
/// sysroot-internal dependencies (`hashbrown`, `std_detect`, ...), which
/// [`def_is_in_real_sysroot_crate`] does not cover because it also requires a
/// sysroot crate NAME.
///
/// The authentication is the same artifact-residency fact
/// (`convert::crate_is_sysroot_resident`), exposed rather than re-spelled so the
/// two cannot drift. It is FALSE for the local crate, for every crate that
/// arrives through `--extern`/`-L` from outside the sysroot (every dependency
/// `targo` builds), and for a crate with no artifact at all.
///
/// Consumer: the verifier's foreign-destructor admission, which credits a
/// bundled destructor's drop glue WITHOUT charging that destructor's body — a
/// credit that is part of the sysroot TCB and must never extend to a
/// dependency's `Drop`.
pub fn def_is_in_sysroot_resident_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    convert::crate_is_sysroot_resident(tcx, def_id.krate)
}

/// Trust (W4 HASHMAP redo, 2026-09-25): is `def_id` defined in the crate that
/// implements THIS compiler's `std::collections::HashMap`/`HashSet` table
/// (`hashbrown`)? Identified STRUCTURALLY — the crate that defines the ADT std's
/// `HashMap`/`HashSet` field is declared as, resolved through std's diagnostic
/// items inside the artifact-authenticated `std` — plus residency, and withdrawn
/// when the crate being compiled names that crate directly (`rustc_private`).
/// Never a crate name. See `convert::crate_is_std_hash_table_implementation`.
///
/// This is the ONLY crate outside `core`/`alloc`/`std` the policy-B vanilla
/// class credits (docs/TCB.md, "hashbrown behind HashMap/HashSet"). It is
/// narrower than [`def_is_in_sysroot_resident_crate`] on purpose: residency also
/// admits `proc_macro`, `test`, `libc`, `std_detect`, ... none of which is
/// credited.
pub fn def_is_in_std_hash_table_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    convert::crate_is_std_hash_table_implementation(tcx, def_id.krate)
}

/// Return an identity-bearing concrete def-path for a monomorphized instance.
///
/// The ordinary rendered path is retained for the common unambiguous crate
/// graph. If two crate instances share a name, the path incorporates rustc's
/// stable crate and full generic-argument identities so display-text
/// collisions cannot merge distinct codegen instances.
pub fn exact_def_path_str_with_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> String {
    let path = safe_def_path_str_with_args(tcx, def_id, args);
    convert::direct_call_def_path(tcx, def_id, args, path)
}

/// Name an extracted callee body in the same domain as its direct call site.
/// Allocation VCs carry an instance-layout byte count on their call names;
/// retain it on the body name too, without removing it from either endpoint.
/// This performs no totality, intrinsic, or trait-call semantic rewrite. The
/// bundler must still resolve the exact instance and compare the full names.
pub fn exact_body_call_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> String {
    convert::with_bulk_alloc_element_size(
        tcx,
        def_id,
        args,
        exact_def_path_str_with_args(tcx, def_id, args),
    )
}

/// Opaque whole-crate authority for paired-condvar wait-site collection.
///
/// This value is constructor-free, non-serializable, and bound to one rustc
/// crate revision. The only minting API below owns the candidate discovery and
/// exhaustive MIR inventory; callers cannot supply functions, candidates, or a
/// raw struct/field map. Bridge consumers receive only opaque exact-site
/// capabilities derived from this token and the current post-transform body.
#[derive(Debug)]
pub struct PairedCondvarCrateCertificate {
    session_seal: Arc<()>,
    certificate_seal: Arc<()>,
    stable_crate_id: u64,
    pairs: FxHashMap<(u64, u64), Vec<(usize, usize)>>,
    // Audit evidence retained in the opaque token. These fields deliberately
    // have no getters: they bind the authority to the exact definitions and
    // extracted bodies inspected by the minting sweep, but are not a second
    // caller-populatable authority surface.
    _condvar_type_defs: FxHashSet<(u64, u64)>,
    _mutex_type_defs: FxHashSet<(u64, u64)>,
    _wait_callee_defs: FxHashSet<(u64, u64)>,
    _inspected_bodies: Vec<PairedCondvarInspectedBody>,
    _licensed_wait_sites: FxHashSet<PairedCondvarLicensedWaitSite>,
}

/// Production authority switch for the paired-condvar semantic lane.
///
/// Keep this false until a real compiler/TyCtxt fixture demonstrates a
/// non-empty certificate and exact-site bridge discharge, and the collector
/// authenticates `Condvar`, `Mutex`, and `Condvar::wait` as definitions from
/// the compiler's genuine sysroot `std` crate (crate identity, not merely a
/// non-local DefId plus rendered path). The synthetic recognizer and sealed-
/// capability tests remain useful while production minting stays dark.
pub const PAIRED_CONDVAR_AUTHORITY_AVAILABLE: bool = false;

/// Canonical digest used to bind an extractor-minted call-site capability to
/// the exact [`VerifiableBody`] later consumed by the bridge.
#[doc(hidden)]
pub fn paired_condvar_body_digest(body: &VerifiableBody) -> Option<String> {
    serde_json::to_vec(body).ok().map(|bytes| stable_sha256_hex(&bytes))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PairedCondvarInspectedBody {
    _owner: (u64, u64),
    _promoted: Option<usize>,
    _mir_digest: String,
}

/// One genuine std wait call observed by the no-caller-input pre-transform
/// crate inventory. Post-transform collection must match this complete record
/// in addition to revalidating the current MIR receiver shape. Keeping the
/// original body digest in the record makes its provenance back to the exact
/// inspected body explicit without pretending pre- and post-transform MIR are
/// byte-identical.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PairedCondvarLicensedWaitSite {
    _owner: (u64, u64),
    _promoted: Option<usize>,
    _block: usize,
    _callee_def: (u64, u64),
    _callee: String,
    _source_span: SourceSpan,
    _receiver_place: String,
    _guard_place: String,
    _inspected_mir_digest: String,
}

impl PairedCondvarLicensedWaitSite {
    fn matches_current_identity(
        &self,
        owner: (u64, u64),
        promoted: Option<usize>,
        block: usize,
        callee_def: (u64, u64),
        callee: &str,
        source_span: &SourceSpan,
        receiver_place: &str,
        guard_place: &str,
    ) -> bool {
        self._owner == owner
            && self._promoted == promoted
            && self._block == block
            && self._callee_def == callee_def
            && self._callee == callee
            && self._source_span == *source_span
            && self._receiver_place == receiver_place
            && self._guard_place == guard_place
    }
}

/// Generic MIR definitions are not an exhaustive inventory of the concrete
/// instances that codegen may create. Until this lane owns that instance set,
/// one generic local body darkens the whole optional certificate.
fn paired_condvar_generic_body_keeps_lane_dark(generic_parameter_count: usize) -> bool {
    generic_parameter_count != 0
}

#[derive(Default)]
struct PairedCondvarSessionSeal(Option<Arc<()>>);

fn paired_condvar_session_seal(tcx: TyCtxt<'_>) -> Arc<()> {
    tcx.sess.with_trust_compiler_state::<PairedCondvarSessionSeal, _>(|state| {
        Arc::clone(state.0.get_or_insert_with(|| Arc::new(())))
    })
}

fn paired_def_key(tcx: TyCtxt<'_>, def_id: DefId) -> (u64, u64) {
    let hash = tcx.def_path_hash(def_id);
    (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}

fn local_item_has_direct_trust_attr(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    #[allow(deprecated)]
    tcx.get_all_attrs(def_id).iter().any(|attr| {
        matches!(
            attr.path().as_slice(),
            [tool, attr_name] if tool.as_str() == "trust" && attr_name.as_str() == name
        )
    })
}

fn empty_paired_condvar_crate_certificate(tcx: TyCtxt<'_>) -> PairedCondvarCrateCertificate {
    PairedCondvarCrateCertificate {
        session_seal: paired_condvar_session_seal(tcx),
        certificate_seal: Arc::new(()),
        stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        pairs: FxHashMap::default(),
        _condvar_type_defs: FxHashSet::default(),
        _mutex_type_defs: FxHashSet::default(),
        _wait_callee_defs: FxHashSet::default(),
        _inspected_bodies: Vec::new(),
        _licensed_wait_sites: FxHashSet::default(),
    }
}

/// Record one exact body and every genuine `std::sync::Condvar::wait` site it
/// contains. Any genuine wait that cannot be mapped one-to-one into the freshly
/// extracted body invalidates the entire crate certificate. Local lookalikes
/// are intentionally ignored: DefId identity, not rendered source text, decides
/// whether a call is licensable.
fn record_paired_body_inventory<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    function: &VerifiableFunction,
    promoted: Option<usize>,
    certificate: &mut PairedCondvarCrateCertificate,
) -> bool {
    let Some(mir_digest) = paired_condvar_body_digest(&function.body) else {
        return false;
    };
    let owner = body.source.def_id();
    let owner_key = paired_def_key(tcx, owner);
    if function.def_path != safe_def_path_str(tcx, owner) {
        return false;
    }

    let mut wait_defs = FxHashSet::default();
    let mut licensed_sites = Vec::new();
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, .. } = &block.terminator().kind else {
            continue;
        };
        let mir::Operand::Constant(constant) = func else { continue };
        let rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
            continue;
        };
        if !def_id.is_local() && safe_def_path_str(tcx, *def_id) == "std::sync::Condvar::wait" {
            let mir::TerminatorKind::Call { args, .. } = &block.terminator().kind else {
                return false;
            };
            if args.len() != 2 {
                return false;
            }
            let callee = convert::func_operand_name_in_body(tcx, body, func);
            let mut lowered_blocks =
                function.body.blocks.iter().filter(|b| b.id.0 == bb.as_usize());
            let Some(lowered_block) = lowered_blocks.next() else {
                return false;
            };
            if lowered_blocks.next().is_some() {
                return false;
            }
            let Terminator::Call { func: lowered, span, .. } = &lowered_block.terminator else {
                return false;
            };
            if *lowered != callee {
                return false;
            }
            let callee_def = paired_def_key(tcx, *def_id);
            wait_defs.insert(callee_def);
            licensed_sites.push(PairedCondvarLicensedWaitSite {
                _owner: owner_key,
                _promoted: promoted,
                _block: bb.as_usize(),
                _callee_def: callee_def,
                _callee: callee,
                _source_span: span.clone(),
                _receiver_place: format!("{:?}", args[0].node),
                _guard_place: format!("{:?}", args[1].node),
                _inspected_mir_digest: mir_digest.clone(),
            });
        }
    }

    let inspected = PairedCondvarInspectedBody {
        _owner: owner_key,
        _promoted: promoted,
        _mir_digest: mir_digest,
    };
    if certificate
        ._inspected_bodies
        .iter()
        .any(|existing| existing._owner == owner_key && existing._promoted == promoted)
    {
        return false;
    }
    if licensed_sites.iter().any(|site| certificate._licensed_wait_sites.contains(site)) {
        return false;
    }
    certificate._wait_callee_defs.extend(wait_defs);
    certificate._licensed_wait_sites.extend(licensed_sites);
    certificate._inspected_bodies.push(inspected);
    true
}

/// Mint the paired-condvar authority for exactly this rustc crate revision.
///
/// The function accepts no caller-provided bodies, candidates, or certificate
/// map. It inventories every local MIR key and promoted body itself and returns
/// an empty (non-authorizing) token on every stolen body, unclassified def kind,
/// const-context gap, std/core/alloc impersonation, unsupported extracted MIR,
/// or semantic certification failure.
#[must_use]
#[allow(rustc::untracked_query_information, rustc::potential_query_instability)]
pub fn certify_paired_condvars_for_crate(tcx: TyCtxt<'_>) -> PairedCondvarCrateCertificate {
    let mut certificate = empty_paired_condvar_crate_certificate(tcx);
    if !PAIRED_CONDVAR_AUTHORITY_AVAILABLE {
        return certificate;
    }
    let mut candidates = Vec::new();
    let mut candidate_keys = FxHashMap::default();
    for item in tcx.hir_crate_items(()).free_items() {
        let did = item.owner_id.to_def_id();
        if !matches!(tcx.def_kind(did), DefKind::Struct)
            || !local_item_has_direct_trust_attr(tcx, did, "paired")
        {
            continue;
        }
        let adt = tcx.adt_def(did);
        if !adt.is_struct() {
            continue;
        }
        let variant = adt.non_enum_variant();
        if variant.ctor.is_some() {
            continue;
        }
        let args = ty::GenericArgs::identity_for_item(tcx, did);
        let mut condvar_fields = Vec::new();
        let mut mutex_fields = Vec::new();
        let mut public_condvar = false;
        for (idx, field) in variant.fields.iter_enumerated() {
            let field_ty = field.ty(tcx, args).skip_normalization();
            let ty::Adt(field_adt, _) = field_ty.kind() else { continue };
            if field_adt.did().is_local() {
                continue;
            }
            match safe_def_path_str(tcx, field_adt.did()).as_str() {
                "std::sync::Condvar" => {
                    certificate._condvar_type_defs.insert(paired_def_key(tcx, field_adt.did()));
                    if field.vis.is_public() {
                        public_condvar = true;
                    } else {
                        condvar_fields.push(idx.as_usize());
                    }
                }
                "std::sync::Mutex" if !field.vis.is_public() => {
                    certificate._mutex_type_defs.insert(paired_def_key(tcx, field_adt.did()));
                    mutex_fields.push(idx.as_usize());
                }
                _ => {}
            }
        }
        if !public_condvar && !condvar_fields.is_empty() && !mutex_fields.is_empty() {
            let struct_name = safe_def_path_str(tcx, did);
            candidate_keys.insert(struct_name.clone(), paired_def_key(tcx, did));
            candidates.push(trust_vcgen::PairedCondvarCandidate {
                struct_name,
                condvar_fields,
                mutex_fields,
                field_count: variant.fields.len(),
            });
        }
    }
    if candidates.is_empty() {
        return certificate;
    }

    for def_id in tcx.hir_crate_items(()).definitions() {
        let path = safe_def_path_str(tcx, def_id.to_def_id());
        if path.starts_with("std::") || path.starts_with("core::") || path.starts_with("alloc::") {
            certificate.pairs.clear();
            return certificate;
        }
    }

    let mut functions = Vec::new();
    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        // Generic MIR definitions are not a monomorphized-instance inventory.
        // Check every MIR key before any def-kind/trivial-const fast path so a
        // generic closure, constructor, or otherwise-skipped const cannot evade
        // the whole-lane-dark rule.
        if paired_condvar_generic_body_keeps_lane_dark(tcx.generics_of(def_id).count()) {
            certificate.pairs.clear();
            return certificate;
        }
        let body = match tcx.def_kind(def_id) {
            DefKind::Ctor(..) => continue,
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
                match tcx.hir_body_const_context(local_def_id) {
                    None | Some(rustc_hir::ConstContext::ConstFn) => {
                        let steal = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
                        if steal.is_stolen() {
                            certificate.pairs.clear();
                            return certificate;
                        }
                        let borrowed = steal.borrow();
                        let function = extract_function_with_contract_bundle(tcx, &borrowed, None);
                        if !record_paired_body_inventory(
                            tcx,
                            &borrowed,
                            &function,
                            None,
                            &mut certificate,
                        ) {
                            certificate.pairs.clear();
                            return certificate;
                        }
                        functions.push(function);
                        None
                    }
                    Some(_) => {
                        certificate.pairs.clear();
                        return certificate;
                    }
                }
            }
            DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
           
            | DefKind::Static { .. } => {
                if tcx.is_trivial_const(local_def_id) {
                    continue;
                }
                Some(tcx.mir_for_ctfe(local_def_id))
            }
            _ => {
                certificate.pairs.clear();
                return certificate;
            }
        };
        if let Some(body) = body {
            let function = extract_function_with_contract_bundle(tcx, body, None);
            if !record_paired_body_inventory(tcx, body, &function, None, &mut certificate) {
                certificate.pairs.clear();
                return certificate;
            }
            functions.push(function);
        }
        for (promoted_index, promoted) in tcx.promoted_mir(def_id).iter().enumerate() {
            let function = extract_function_with_contract_bundle(tcx, promoted, None);
            if !record_paired_body_inventory(
                tcx,
                promoted,
                &function,
                Some(promoted_index),
                &mut certificate,
            ) {
                certificate.pairs.clear();
                return certificate;
            }
            functions.push(function);
        }
    }

    for pair in trust_vcgen::certify_paired_condvars(&functions, &candidates) {
        let Some(&struct_key) = candidate_keys.get(&pair.struct_name) else {
            certificate.pairs.clear();
            return certificate;
        };
        certificate
            .pairs
            .entry(struct_key)
            .or_default()
            .push((pair.condvar_field, pair.mutex_field));
    }
    certificate
}

#[cfg(test)]
mod paired_condvar_authority_tests {
    use super::*;

    fn licensed_site() -> PairedCondvarLicensedWaitSite {
        PairedCondvarLicensedWaitSite {
            _owner: (1, 2),
            _promoted: None,
            _block: 3,
            _callee_def: (4, 5),
            _callee: "std::sync::Condvar::wait::<u64>".into(),
            _source_span: SourceSpan {
                file: "paired.rs".into(),
                line_start: 10,
                col_start: 2,
                line_end: 10,
                col_end: 24,
            },
            _receiver_place: "move _7".into(),
            _guard_place: "move _8".into(),
            _inspected_mir_digest: "pre-transform-body-digest".into(),
        }
    }

    #[test]
    fn generic_body_keeps_whole_paired_condvar_lane_dark() {
        assert!(!paired_condvar_generic_body_keeps_lane_dark(0));
        assert!(paired_condvar_generic_body_keeps_lane_dark(1));
        assert!(paired_condvar_generic_body_keeps_lane_dark(usize::MAX));
    }

    #[test]
    fn paired_condvar_production_authority_stays_dark_pending_real_tycx_positive() {
        assert!(!PAIRED_CONDVAR_AUTHORITY_AVAILABLE);
    }

    #[test]
    fn stale_or_mutated_wait_site_never_matches_the_license() {
        let site = licensed_site();
        let exact = |block, callee: &str, span: &SourceSpan, receiver: &str, guard: &str| {
            site.matches_current_identity(
                (1, 2),
                None,
                block,
                (4, 5),
                callee,
                span,
                receiver,
                guard,
            )
        };
        assert!(exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!exact(
            4,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u32>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        let mut moved_span = site._source_span.clone();
        moved_span.line_start += 1;
        assert!(!exact(3, "std::sync::Condvar::wait::<u64>", &moved_span, "move _7", "move _8",));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _70",
            "move _8",
        ));
        assert!(!exact(
            3,
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _80",
        ));
        assert!(!site.matches_current_identity(
            (9, 9),
            None,
            3,
            (4, 5),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!site.matches_current_identity(
            (1, 2),
            Some(0),
            3,
            (4, 5),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
        assert!(!site.matches_current_identity(
            (1, 2),
            None,
            3,
            (9, 9),
            "std::sync::Condvar::wait::<u64>",
            &site._source_span,
            "move _7",
            "move _8",
        ));
    }
}

/// Error returned when a compiler-native Trust contract bundle cannot be
/// converted into the rustc-independent `trust-types` model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustContractBundleConversionError {
    /// The bundle summary claims contracts exist, but the dense contract list
    /// is empty. Treat this as unavailable data rather than a successful empty
    /// extraction.
    NonConvertibleNonEmptyBundle { summary_total: u32 },
    /// The query summary and the actual function-plus-loop storage disagree.
    /// Treat the bundle as corrupt rather than trusting either partial view.
    SummaryCardinalityMismatch { summary_total: u32, actual_total: usize },
    /// The compiler contract kind has no equivalent in `trust-types::Contract`.
    UnsupportedContractKind { index: usize, kind: String },
    /// The compiler contract is anchored somewhere the current target model
    /// cannot represent without losing information.
    UnsupportedSubject { index: usize, subject: String },
    /// The compiler predicate is explicitly marked unsupported.
    UnsupportedPredicate { index: usize, reason: String },
    /// The predicate points at a MIR local value that has not been lowered to a
    /// stable textual or structured contract expression yet.
    MirLocalPredicate { index: usize, local: usize },
}

pub(crate) use trust_source_contract::{
    LOWERED_COMPILER_CONTRACT_PREFIX, UNSUPPORTED_COMPILER_CONTRACT_PREFIX,
};

impl std::fmt::Display for TrustContractBundleConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonConvertibleNonEmptyBundle { summary_total } => write!(
                f,
                "Trust contract bundle summary reports {summary_total} contracts but no convertible contract entries are present"
            ),
            Self::SummaryCardinalityMismatch { summary_total, actual_total } => write!(
                f,
                "Trust contract bundle summary reports {summary_total} contracts but contains {actual_total} function and loop contract entries"
            ),
            Self::UnsupportedContractKind { index, kind } => {
                write!(f, "Trust contract #{index} has unsupported kind {kind}")
            }
            Self::UnsupportedSubject { index, subject } => {
                write!(f, "Trust contract #{index} has unsupported subject {subject}")
            }
            Self::UnsupportedPredicate { index, reason } => {
                write!(f, "Trust contract #{index} has unsupported predicate: {reason}")
            }
            Self::MirLocalPredicate { index, local } => {
                write!(f, "Trust contract #{index} uses non-convertible MIR local _{local}")
            }
        }
    }
}

impl std::error::Error for TrustContractBundleConversionError {}

/// A MIR construct that the verification-oriented TrustIr can abstract, but
/// the executable trust-cg path cannot reproduce byte-for-byte.
///
/// Codegen must never continue past this error: doing so would verify one
/// abstract program and emit another executable program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenExtractionError {
    /// Extraction changed executable control flow (for example, rewriting
    /// `std::process::exit` into an ordinary Rust return).
    SemanticAbstraction { def_path: String, block: usize, detail: String },
    /// TrustIr contains a sentinel, placeholder, or layout-erased construct
    /// whose runtime meaning is not fully represented.
    UnsupportedMir { def_path: String, location: String, detail: String },
    /// Extraction changed the body topology, so MIR and TrustIr can no longer
    /// be related block-for-block.
    StructuralMismatch { def_path: String, detail: String },
}

impl std::fmt::Display for CodegenExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SemanticAbstraction { def_path, block, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` failed at bb{block}: {detail}"
                )
            }
            Self::UnsupportedMir { def_path, location, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` failed at {location}: {detail}"
                )
            }
            Self::StructuralMismatch { def_path, detail } => {
                write!(
                    f,
                    "codegen-faithful extraction of `{def_path}` changed MIR structure: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for CodegenExtractionError {}

/// Convert a compiler-native Trust contract bundle into the rustc-independent
/// `trust-types` bundle consumed by MIR extraction.
///
/// This conversion is intentionally fail-closed. Whole-function
/// `Requires`/`Ensures`/`Decreases` clauses retain their dense compiler index,
/// while E4/E5 loop clauses are carried in the parallel `loop_contracts` lane
/// with their loop-head spans. Predicates may be opaque text, boolean literals,
/// or explicit unsupported payloads; unsupported predicates are preserved so
/// VC generation creates a visible per-clause Unknown instead of dropping
/// authored semantics.
pub fn convert_trust_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    bundle: &rustc_trust_contract::TrustContractBundle<'tcx>,
) -> Result<CompilerContractBundle, TrustContractBundleConversionError> {
    if bundle.is_empty() {
        return if bundle.summary.total == 0 {
            Ok(CompilerContractBundle::default())
        } else {
            Err(TrustContractBundleConversionError::NonConvertibleNonEmptyBundle {
                summary_total: bundle.summary.total,
            })
        };
    }

    let actual_total = bundle.len();
    if bundle.summary.total as usize != actual_total {
        return Err(TrustContractBundleConversionError::SummaryCardinalityMismatch {
            summary_total: bundle.summary.total,
            actual_total,
        });
    }

    let mut contracts = Vec::with_capacity(bundle.contracts.len());
    let mut typed_propositions = Vec::new();
    // Preserve `TrustContractId` order exactly. Downstream native TrustIr lowering
    // reconstructs stable source/assertion ids from this dense contract index.
    for (id, contract) in bundle.contracts.iter_enumerated() {
        let index = id.as_usize();
        let kind = convert_trust_contract_kind(index, contract.kind)?;
        convert_trust_contract_subject(index, contract.subject)?;
        let (body, proposition) =
            convert_trust_contract_predicate(index, contract.kind, &contract.predicate.kind)?;
        if let Some((formula, variable_domains)) = proposition {
            typed_propositions.push(trust_types::CompilerContractProposition {
                source_contract_index: index,
                kind,
                body: body.clone(),
                formula,
                variable_domains,
            });
        }
        contracts.push(Contract { kind, span: convert::convert_span(tcx, contract.span), body });
    }

    let mut loop_contracts = Vec::with_capacity(bundle.loop_contracts.len());
    for (index, contract) in bundle.loop_contracts.iter().enumerate() {
        let global_index = bundle.contracts.len() + index;
        let kind = match contract.kind {
            rustc_trust_contract::TrustContractKind::LoopInvariant => {
                trust_types::LoopContractKind::Invariant
            }
            rustc_trust_contract::TrustContractKind::Decreases => {
                trust_types::LoopContractKind::Decreases
            }
            kind => {
                return Err(TrustContractBundleConversionError::UnsupportedContractKind {
                    index,
                    kind: format!("{kind:?}"),
                });
            }
        };
        let rustc_trust_contract::TrustContractSubject::HirLoop { id, loop_span, header_span } =
            contract.subject
        else {
            return Err(TrustContractBundleConversionError::UnsupportedSubject {
                index,
                subject: format!("{:?}", contract.subject),
            });
        };
        let (body, proposition) = convert_trust_contract_predicate(
            global_index,
            contract.kind,
            &contract.predicate.kind,
        )?;
        let portable_kind = match kind {
            trust_types::LoopContractKind::Invariant => ContractKind::LoopInvariant,
            trust_types::LoopContractKind::Decreases => ContractKind::Decreases,
        };
        if let Some((formula, variable_domains)) = proposition {
            typed_propositions.push(trust_types::CompilerContractProposition {
                source_contract_index: global_index,
                kind: portable_kind,
                body: body.clone(),
                formula,
                variable_domains,
            });
        }
        loop_contracts.push(trust_types::LoopContractSpec {
            kind,
            source_loop_id: id.index,
            source_hir_local_id: Some(id.hir_local_id),
            mir_header: None,
            loop_head: convert::convert_span(tcx, loop_span),
            header_span: convert::convert_span(tcx, header_span),
            span: convert::convert_span(tcx, contract.span),
            body,
        });
    }

    Ok(CompilerContractBundle::new(contracts)
        .with_typed_propositions(typed_propositions)
        .with_loop_contracts(loop_contracts))
}

/// Bind compiler-owned source-loop identities to exact MIR natural-loop
/// headers in the same rustc body.
///
/// The contract query carries the loop expression's HIR-local id. MIR building
/// stamps the source scope used while lowering that expression. MIR
/// simplification can retain the stamp on either endpoint of a
/// dominator-proved backedge, so either endpoint may nominate its exact natural
/// header. When both endpoint stamps survive they must agree, and the final
/// HIR-id/header mapping must also be injective across source-loop groups.
/// Thus cross-loop endpoint pairs reject directly and distinct source groups
/// cannot merge their authority later. Neither spans nor block allocation
/// order participate. The resulting `mir_header` remains redundant provenance:
/// vcgen re-detects the natural loop and rejects a stale/non-header block before
/// using it.
///
/// A miss leaves the field empty and returns a stable blocker code. This is
/// intentionally fail-closed and lets legacy single-loop bundles retain their
/// existing span fallback without granting nested-loop authority.
///
/// # Cross-crate inlined scopes are a MISS, never a stamp
///
/// A body that is entirely local can still contain source scopes that came from
/// another crate: the MIR inliner APPENDS the callee's `source_scopes` verbatim
/// into the caller (`rustc_mir_transform::inline`), and a callee decoded from
/// crate metadata carries `ClearCrossCrate::Clear` because crate-local scope
/// data is deliberately never encoded cross-crate. Every backedge with such an
/// endpoint is dropped here and counted; the count refines the blocker code so
/// the resulting miss names the real cause instead of reading as "this HIR loop
/// has no natural MIR loop". See [`ScopeLoopIdentity`] for why a cleared scope
/// must not be flattened into the ordinary unstamped-scope case.
pub fn stamp_loop_header_provenance(
    body: &mir::Body<'_>,
    bundle: &mut CompilerContractBundle,
) -> Vec<(u32, String)> {
    if bundle.loop_contracts.is_empty() {
        return Vec::new();
    }
    let dominators = body.basic_blocks.dominators();
    let mut backedges = Vec::new();
    let mut cross_crate_opaque_backedges = 0usize;
    for (latch, block) in body.basic_blocks.iter_enumerated() {
        if !dominators.is_reachable(latch) {
            continue;
        }
        for header in block.terminator().successors() {
            if !dominators.dominates(header, latch) {
                continue;
            }
            let (
                ScopeLoopIdentity::CrateLocal(header_hir_local_id),
                ScopeLoopIdentity::CrateLocal(latch_hir_local_id),
            ) = (source_loop_local_id(body, header), source_loop_local_id(body, latch))
            else {
                // Fail closed and stay countable: an endpoint whose scope data
                // was cleared cross-crate can neither nominate a header nor be
                // nominated as one, because this crate holds no HIR-loop
                // identity for it and may not invent one.
                cross_crate_opaque_backedges += 1;
                continue;
            };
            backedges.push(StampedNaturalBackedge {
                header: header.as_usize(),
                header_hir_local_id,
                latch_hir_local_id,
            });
        }
    }

    stamp_loop_header_provenance_from_backedges(&backedges, cross_crate_opaque_backedges, bundle)
}

/// A backedge endpoint's Trust loop identity, as far as THIS crate can know it.
///
/// `SourceScopeData::local_data` is a `ClearCrossCrate`, and the two states are
/// NOT interchangeable for provenance:
///
/// * `CrateLocal(None)` means this crate saw the scope and the scope carried no
///   Trust loop stamp. The other endpoint of the backedge may still nominate
///   the header — that is the documented one-sided-stamp rule above.
/// * `ClearedCrossCrate` means this crate never had the data at all. Reading it
///   as `CrateLocal(None)` would silently promote "unknown" to "known to carry
///   no stamp" and let the opposite endpoint bind a block from inlined foreign
///   MIR as an authored loop's header, which nothing here can substantiate.
///
/// Unwrapping the cleared case instead of matching it is what ICEd the whole
/// third-party verification lane: `unwrap_crate_local` is `bug!("unwrapping
/// cross-crate data")`.
enum ScopeLoopIdentity {
    /// This crate holds the scope's local data; the payload is the authored
    /// loop's HIR-local id when the scope carries one.
    CrateLocal(Option<u32>),
    /// The scope arrived with cross-crate inlined MIR and its crate-local data
    /// was cleared. No identity exists here.
    ClearedCrossCrate,
}

fn source_loop_local_id(body: &mir::Body<'_>, block: mir::BasicBlock) -> ScopeLoopIdentity {
    let scope = &body.source_scopes[body.basic_blocks[block].terminator().source_info.scope];
    // A scope inlined from a callee carries the CALLEE's stamp: a bare per-owner
    // `ItemLocalId` that can equal one of this body's loops (review round 42: an
    // inlined helper's `while` was taken as the header of a caller `loop { break; }`
    // with the same local id, and the caller's invariant was certified at the
    // helper's loop head). It names no loop of this body: unstamped.
    if scope.inlined.is_some() || scope.inlined_parent_scope.is_some() {
        return ScopeLoopIdentity::CrateLocal(None);
    }
    match scope.local_data.as_ref() {
        mir::ClearCrossCrate::Set(local_data) => ScopeLoopIdentity::CrateLocal(
            local_data.trust_loop_hir_local_id.map(|local_id| local_id.as_u32()),
        ),
        mir::ClearCrossCrate::Clear => ScopeLoopIdentity::ClearedCrossCrate,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StampedNaturalBackedge {
    header: usize,
    header_hir_local_id: Option<u32>,
    latch_hir_local_id: Option<u32>,
}

/// `cross_crate_opaque_backedges` is the number of dominator-proved backedges
/// that were DROPPED before candidacy because an endpoint's source-scope data
/// was cleared by cross-crate MIR inlining. It never admits a header; it only
/// makes the resulting refusal name its cause.
fn stamp_loop_header_provenance_from_backedges(
    backedges: &[StampedNaturalBackedge],
    cross_crate_opaque_backedges: usize,
    bundle: &mut CompilerContractBundle,
) -> Vec<(u32, String)> {
    // This function is also a restamping boundary for the public portable
    // bundle. Never let a failed or changed body retain authority minted by a
    // previous invocation.
    for spec in &mut bundle.loop_contracts {
        spec.mir_header = None;
    }

    let mut source_ids =
        bundle.loop_contracts.iter().map(|spec| spec.source_loop_id).collect::<Vec<_>>();
    source_ids.sort_unstable();
    source_ids.dedup();

    let mut decisions = FxHashMap::<u32, Result<usize, String>>::default();
    let mut group_hir_ids = FxHashMap::<u32, u32>::default();
    for &source_loop_id in &source_ids {
        let group = bundle
            .loop_contracts
            .iter()
            .filter(|spec| spec.source_loop_id == source_loop_id)
            .collect::<Vec<_>>();
        let Some(first) = group.first() else { continue };
        let Some(hir_local_id) = first.source_hir_local_id else {
            decisions.insert(
                source_loop_id,
                Err(
                    "e45.loop-source.missing-hir-id: compiler loop clause has no HIR-local identity"
                        .to_string(),
                ),
            );
            continue;
        };
        if group.iter().any(|spec| spec.source_hir_local_id != Some(hir_local_id)) {
            decisions.insert(
                source_loop_id,
                Err(
                    "e45.loop-source.inconsistent-hir-id: clauses on one source loop disagree on HIR identity"
                        .to_string(),
                ),
            );
            continue;
        }
        group_hir_ids.insert(source_loop_id, hir_local_id);
    }

    // `TrustLoopId::index` and its HIR identity are both compiler-minted
    // per-function identities. Two distinct source groups claiming one HIR
    // loop would otherwise share all downstream header authority.
    let mut hir_owners = FxHashMap::<u32, Vec<u32>>::default();
    for (&source_loop_id, &hir_local_id) in &group_hir_ids {
        hir_owners.entry(hir_local_id).or_default().push(source_loop_id);
    }
    for (hir_local_id, mut owners) in hir_owners {
        if owners.len() < 2 {
            continue;
        }
        owners.sort_unstable();
        let reason = format!(
            "e45.loop-source.non-injective-hir-id: HIR loop {hir_local_id} is claimed by source loop groups {owners:?}"
        );
        for source_loop_id in owners {
            decisions.insert(source_loop_id, Err(reason.clone()));
        }
    }

    for &source_loop_id in &source_ids {
        if decisions.contains_key(&source_loop_id) {
            continue;
        }
        let Some(&hir_local_id) = group_hir_ids.get(&source_loop_id) else {
            continue;
        };
        let mut candidates = backedges
            .iter()
            .filter_map(|backedge| {
                let endpoints_compatible =
                    match (backedge.header_hir_local_id, backedge.latch_hir_local_id) {
                        (Some(header_id), Some(latch_id)) => header_id == latch_id,
                        _ => true,
                    };
                (endpoints_compatible
                    && (backedge.header_hir_local_id == Some(hir_local_id)
                        || backedge.latch_hir_local_id == Some(hir_local_id)))
                .then_some(backedge.header)
            })
            .collect::<Vec<_>>();
        candidates.sort_unstable();
        candidates.dedup();
        let decision = match candidates.as_slice() {
            [header] => Ok(*header),
            // A miss in a body that also carries cross-crate-cleared backedges
            // must not be reported as "this loop has no natural MIR header":
            // the dropped edges are exactly the ones this crate could not read,
            // so the honest verdict is that the mapping is UNAVAILABLE here.
            // Still fail-closed — no header is bound either way.
            [] if cross_crate_opaque_backedges > 0 => Err(format!(
                "e45.loop-source.cross-crate-inlined-scope: HIR loop {hir_local_id} matched no \
                 readable dominator-proved MIR header; {cross_crate_opaque_backedges} \
                 dominator-proved backedge(s) in this body carry source-scope data cleared by \
                 cross-crate MIR inlining and can authorize nothing"
            )),
            _ => {
                let code = if candidates.is_empty() {
                    "e45.loop-source.no-mir-header"
                } else {
                    "e45.loop-source.ambiguous-mir-header"
                };
                Err(format!(
                    "{code}: HIR loop {hir_local_id} matched {} dominator-proved MIR header(s)",
                    candidates.len()
                ))
            }
        };
        decisions.insert(source_loop_id, decision);
    }

    // Header identity must be injective across source-loop groups. Runtime
    // certified-monitor placement groups clauses by this header, so allowing
    // two source identities to share it would silently merge their monitors.
    let mut header_owners = FxHashMap::<usize, Vec<u32>>::default();
    for (&source_loop_id, decision) in &decisions {
        if let Ok(header) = decision {
            header_owners.entry(*header).or_default().push(source_loop_id);
        }
    }
    for (header, mut owners) in header_owners {
        if owners.len() < 2 {
            continue;
        }
        owners.sort_unstable();
        let reason = format!(
            "e45.loop-source.non-injective-mir-header: MIR header bb{header} is claimed by source loop groups {owners:?}"
        );
        for source_loop_id in owners {
            decisions.insert(source_loop_id, Err(reason.clone()));
        }
    }

    let mut failures = Vec::new();
    for source_loop_id in source_ids {
        let Some(decision) = decisions.remove(&source_loop_id) else {
            failures.push((
                source_loop_id,
                "e45.loop-source.missing-binding-decision: compiler loop group has no provenance decision"
                    .to_string(),
            ));
            continue;
        };
        match decision {
            Ok(header) => {
                for spec in bundle
                    .loop_contracts
                    .iter_mut()
                    .filter(|spec| spec.source_loop_id == source_loop_id)
                {
                    spec.mir_header = Some(header);
                }
            }
            Err(reason) => failures.push((source_loop_id, reason)),
        }
    }
    failures
}

fn convert_trust_contract_kind(
    index: usize,
    kind: rustc_trust_contract::TrustContractKind,
) -> Result<ContractKind, TrustContractBundleConversionError> {
    match kind {
        rustc_trust_contract::TrustContractKind::Requires => Ok(ContractKind::Requires),
        rustc_trust_contract::TrustContractKind::Ensures => Ok(ContractKind::Ensures),
        rustc_trust_contract::TrustContractKind::Decreases => Ok(ContractKind::Decreases),
        _ => Err(TrustContractBundleConversionError::UnsupportedContractKind {
            index,
            kind: format!("{kind:?}"),
        }),
    }
}

fn convert_trust_contract_subject(
    index: usize,
    subject: rustc_trust_contract::TrustContractSubject,
) -> Result<(), TrustContractBundleConversionError> {
    match subject {
        rustc_trust_contract::TrustContractSubject::Function => Ok(()),
        _ => Err(TrustContractBundleConversionError::UnsupportedSubject {
            index,
            subject: format!("{subject:?}"),
        }),
    }
}

fn convert_trust_contract_predicate(
    index: usize,
    kind: rustc_trust_contract::TrustContractKind,
    predicate: &rustc_trust_contract::TrustContractPredicateKind,
) -> Result<
    (String, Option<(Formula, Vec<trust_types::CompilerContractVariableDomain>)>),
    TrustContractBundleConversionError,
> {
    let expected_class = if kind == rustc_trust_contract::TrustContractKind::Decreases {
        trust_types::CompilerContractExpressionClass::Measure
    } else {
        trust_types::CompilerContractExpressionClass::Proposition
    };
    match predicate {
        rustc_trust_contract::TrustContractPredicateKind::Typed { text, proposition } => {
            let body = text.to_string();
            let (formula, variable_domains) =
                trust_contract_proposition_to_formula_and_domains_for_class(
                    proposition,
                    expected_class,
                )
                .map_err(|reason| {
                    TrustContractBundleConversionError::UnsupportedPredicate { index, reason }
                })?;
            let Some(source) = body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX) else {
                return Err(TrustContractBundleConversionError::UnsupportedPredicate {
                    index,
                    reason: "typed compiler proposition is missing its canonical lowering prefix"
                        .to_string(),
                });
            };
            let round_trip = trust_types::parse_spec_expr(source).and_then(|parsed| {
                trust_types::compiler_contract_formula_with_domains_for_class(
                    &parsed,
                    &variable_domains,
                    expected_class,
                )
            });
            if round_trip.as_ref() != Some(&formula) {
                return Err(TrustContractBundleConversionError::UnsupportedPredicate {
                    index,
                    reason: "typed compiler proposition does not structurally match its canonical source spelling"
                        .to_string(),
                });
            }
            Ok((body, Some((formula, variable_domains))))
        }
        rustc_trust_contract::TrustContractPredicateKind::Opaque { text } => {
            Ok((text.to_string(), None))
        }
        rustc_trust_contract::TrustContractPredicateKind::BoolLiteral { value } => {
            if expected_class == trust_types::CompilerContractExpressionClass::Measure {
                Err(TrustContractBundleConversionError::UnsupportedPredicate {
                    index,
                    reason: "decreases clause has a Boolean predicate instead of a numeric measure"
                        .to_string(),
                })
            } else {
                Ok((
                    format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{value}"),
                    Some((Formula::Bool(*value), Vec::new())),
                ))
            }
        }
        rustc_trust_contract::TrustContractPredicateKind::MirLocal { local } => {
            Err(TrustContractBundleConversionError::MirLocalPredicate {
                index,
                local: local.as_usize(),
            })
        }
        rustc_trust_contract::TrustContractPredicateKind::Unsupported { reason } => {
            Ok((format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}{}", reason), None))
        }
    }
}

/// Lossless conversion from the compiler-query proposition into the static
/// verifier formula. No source text is parsed here.
pub fn trust_contract_proposition_to_formula(
    proposition: &rustc_trust_contract::TrustContractProposition,
) -> Formula {
    use rustc_trust_contract::{
        TrustContractProposition as Proposition, TrustContractPropositionDomain as Domain,
    };

    let boxed =
        |proposition: &Proposition| Box::new(trust_contract_proposition_to_formula(proposition));
    match proposition {
        Proposition::Bool(value) => Formula::Bool(*value),
        Proposition::Int(value) => Formula::Int(*value),
        Proposition::UInt(value) => Formula::UInt(*value),
        // The literal is carried by BITS, so it lands as the IEEE constant those
        // bits denote — bit-preserving through the two zeroes and any NaN payload.
        Proposition::Float { bits, width } => match ieee_format_for_width(*width) {
            Some((eb, sb)) => Formula::FpConst { bits: u128::from(*bits), eb, sb },
            None => Formula::Bool(false),
        },
        // A float VARIABLE binds at its IEEE sort, which is the spelling the spec
        // parser already gives a float-compared variable and the one the
        // canonical source round trip compares against. No lift is needed or
        // wanted: `ay_bridge` lowers an ordering comparison by the operands'
        // SORT, so a float-sorted `Le` is already `fp.leq`.
        Proposition::Var { name, domain: Domain::Float { width } } => {
            match Sort::float_for_width(*width) {
                Some(sort) => Formula::Var(name.to_string(), sort),
                None => Formula::Bool(false),
            }
        }
        Proposition::Var { name, domain } => Formula::Var(
            name.to_string(),
            if *domain == Domain::Bool { Sort::Bool } else { Sort::Int },
        ),
        Proposition::Not(inner) => Formula::Not(boxed(inner)),
        Proposition::And(terms) => {
            Formula::And(terms.iter().map(trust_contract_proposition_to_formula).collect())
        }
        Proposition::Or(terms) => {
            Formula::Or(terms.iter().map(trust_contract_proposition_to_formula).collect())
        }
        Proposition::Implies(lhs, rhs) => Formula::Implies(boxed(lhs), boxed(rhs)),
        // ORDERING comparisons and arithmetic stay the PLAIN nodes for floats too.
        // This is not a shortcut: `ay_bridge` lowers an ordering comparison by
        // the operands' sort, so a float-sorted `Le` is `fp.leq` and an integer
        // one is `int_le`.
        //
        // EQUALITY is the exception (SPEC-FLOAT-EQ-STRUCTURAL-1). `Formula::Eq`
        // is structural SMT `=` whatever its sort — `NaN = NaN` holds and
        // `+0 = -0` fails — while the clause's `==` is Rust `PartialEq`. Over a
        // float domain it is therefore IEEE `FpEq`, the same node the parser
        // builds for `x == 1.0` and the domain rebinding builds for `x == y`, so
        // the canonical-source round trip below still compares equal.
        Proposition::Eq(lhs, rhs) => trust_types::spec_equality(boxed(lhs), boxed(rhs)),
        Proposition::Lt(lhs, rhs) => Formula::Lt(boxed(lhs), boxed(rhs)),
        Proposition::Le(lhs, rhs) => Formula::Le(boxed(lhs), boxed(rhs)),
        Proposition::Gt(lhs, rhs) => Formula::Gt(boxed(lhs), boxed(rhs)),
        Proposition::Ge(lhs, rhs) => Formula::Ge(boxed(lhs), boxed(rhs)),
        Proposition::Add(lhs, rhs) => Formula::Add(boxed(lhs), boxed(rhs)),
        Proposition::Sub(lhs, rhs) => Formula::Sub(boxed(lhs), boxed(rhs)),
        Proposition::Mul(lhs, rhs) => Formula::Mul(boxed(lhs), boxed(rhs)),
        Proposition::Div(lhs, rhs) => Formula::Div(boxed(lhs), boxed(rhs)),
        Proposition::Rem(lhs, rhs) => Formula::Rem(boxed(lhs), boxed(rhs)),
        Proposition::Neg(inner) => Formula::Neg(boxed(inner)),
    }
}

/// `(eb, sb)` for a Rust float width, or `None` for a width with no IEEE format
/// in the formula language. A `None` here must reach a refusal, never a fallback
/// to the integer lowering.
fn ieee_format_for_width(width: u32) -> Option<(u32, u32)> {
    match Sort::float_for_width(width) {
        Some(Sort::Float { eb, sb }) => Some((eb, sb)),
        _ => None,
    }
}

/// Convert the query tree while retaining its exact source-domain identity.
/// Conflicting domains for the same canonical variable are rejected instead
/// of choosing an arbitrary occurrence.
pub fn trust_contract_proposition_to_formula_and_domains(
    proposition: &rustc_trust_contract::TrustContractProposition,
) -> Result<(Formula, Vec<trust_types::CompilerContractVariableDomain>), String> {
    trust_contract_proposition_to_formula_and_domains_for_class(
        proposition,
        trust_types::CompilerContractExpressionClass::Proposition,
    )
}

/// Class-aware query-proposition conversion used for Boolean contracts and
/// numeric function/loop decreases measures.
pub fn trust_contract_proposition_to_formula_and_domains_for_class(
    proposition: &rustc_trust_contract::TrustContractProposition,
    expected_class: trust_types::CompilerContractExpressionClass,
) -> Result<(Formula, Vec<trust_types::CompilerContractVariableDomain>), String> {
    use rustc_trust_contract::{
        TrustContractProposition as Proposition, TrustContractPropositionDomain as Domain,
    };
    use trust_types::{CompilerContractValueDomain as ValueDomain, CompilerContractVariableDomain};

    fn collect(
        proposition: &Proposition,
        domains: &mut std::collections::BTreeMap<String, ValueDomain>,
    ) -> Result<(), String> {
        match proposition {
            Proposition::Var { name, domain } => {
                let domain = match domain {
                    Domain::Bool => ValueDomain::Bool,
                    Domain::MathematicalInt => ValueDomain::MathematicalInt,
                    Domain::PointerSizedInt { width, signed } => {
                        ValueDomain::PointerSizedInt { width: *width, signed: *signed }
                    }
                    Domain::MachineInt { width, signed } => {
                        ValueDomain::MachineInt { width: *width, signed: *signed }
                    }
                    Domain::Float { width } => ValueDomain::Float { width: *width },
                };
                let name = name.to_string();
                if let Some(previous) = domains.insert(name.clone(), domain) {
                    if previous != domain {
                        return Err(format!(
                            "typed compiler proposition gives `{name}` conflicting domains {previous:?} and {domain:?}"
                        ));
                    }
                }
            }
            // A literal binds no variable, so it contributes no domain. Listed
            // beside the other literals rather than folded into a wildcard, so a
            // future node that DOES bind one cannot inherit this silence.
            Proposition::Float { .. } => {}
            Proposition::Not(inner) | Proposition::Neg(inner) => collect(inner, domains)?,
            Proposition::And(terms) | Proposition::Or(terms) => {
                for term in terms {
                    collect(term, domains)?;
                }
            }
            Proposition::Implies(lhs, rhs)
            | Proposition::Eq(lhs, rhs)
            | Proposition::Lt(lhs, rhs)
            | Proposition::Le(lhs, rhs)
            | Proposition::Gt(lhs, rhs)
            | Proposition::Ge(lhs, rhs)
            | Proposition::Add(lhs, rhs)
            | Proposition::Sub(lhs, rhs)
            | Proposition::Mul(lhs, rhs)
            | Proposition::Div(lhs, rhs)
            | Proposition::Rem(lhs, rhs) => {
                collect(lhs, domains)?;
                collect(rhs, domains)?;
            }
            Proposition::Bool(_) | Proposition::Int(_) | Proposition::UInt(_) => {}
        }
        Ok(())
    }

    let formula = trust_contract_proposition_to_formula(proposition);
    let mut domains = std::collections::BTreeMap::new();
    collect(proposition, &mut domains)?;
    let variable_domains = domains
        .into_iter()
        .map(|(name, domain)| CompilerContractVariableDomain { name, domain })
        .collect::<Vec<_>>();
    if trust_types::compiler_contract_formula_with_domains_for_class(
        &formula,
        &variable_domains,
        expected_class,
    )
    .as_ref()
        != Some(&formula)
    {
        return Err(
            "typed compiler proposition has an incomplete or non-canonical domain map".to_string()
        );
    }
    Ok((formula, variable_domains))
}

/// Extract a VerifiableFunction from a rustc MIR Body.
///
/// This is the main entry point. Called once per function in the crate.
/// The default native path fails closed when compiler-owned contract facts are
/// unavailable: it will not scrape Rust source files to reconstruct contracts.
/// Trust (v25 B1): FAITHFUL-SCALAR extraction — isize/usize/char keep their identity
/// (`TrustTy::PtrSizedInt`/`TrustTy::Char`) instead of the legacy width
/// collapse. This is the trust-ir DIFFERENTIAL's lane (the bridge maps the
/// faithful spellings onto `trust_ir::Ty::Isize/Usize/Char` so producer and
/// oracle signatures agree by leaf equality). It also bypasses the logical
/// Clean Level/ExprKind/Expr datatype shortcuts, whose pointer-peeling fields
/// are not physical MIR fields; ordinary ADT lowering and its existing limits
/// apply instead. It also retains physical Vec fields rather than the logical
/// sequence abstraction. Real calls are retained instead of verifier-only total
/// summaries or call-shape normalizations. Authenticated exact-operation markers
/// remain. This does not claim that every type or operation is modeled, or that
/// the retained callees' bodies have been proved.
/// The verifier pipeline stays on
/// the legacy entry until its own migration wave.
pub fn extract_function_faithful<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> VerifiableFunction {
    let _guard = crate::ty_convert::FaithfulScalarsGuard::enable();
    extract_function(tcx, body)
}

/// Preserve the compiler allocation namespace of this exact extraction for
/// compiler-owned instance discovery. These ephemeral AllocIds are never a
/// serialized identity or proof; public consumers receive resolved instances
/// through `instance_body` instead.
pub(crate) fn extract_function_faithful_with_allocations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> (VerifiableFunction, Vec<mir::interpret::AllocId>) {
    let _guard = crate::ty_convert::FaithfulScalarsGuard::enable();
    let mut allocations = Vec::new();
    let function = extract_function_with_purpose_observed(
        tcx,
        body,
        None,
        ExtractionPurpose::Verification,
        Some(&mut allocations),
        None,
    );
    (function, allocations)
}

/// Trust (vtable slice 3): FAITHFUL-lane conversion of ONE rustc type, for the
/// vtable-identity SOURCE key.
///
/// The `(principal, source)` vtable identity (`trust_ir::stable_vtable_global_name`)
/// renders its source half with `trust_types::Ty::vtable_source_type_key`, the one
/// shared renderer. The MIR-side bridge calls that renderer on the extractor-recorded
/// local type, which [`extract_function_faithful`] produced under the
/// `FaithfulScalarsGuard`; the THIR producer holds a rustc type instead, and THIS is
/// its conversion entry — the SAME `convert_ty_in_env` under the SAME guard — so the
/// two sides render one string for one rustc source type BY CONSTRUCTION (the
/// `trait_object_id` lesson: never a second hand-rolled producer of one identity).
///
/// The caller passes the coercion source's NORMALIZED pointee (the producer
/// normalizes under `TypingEnv::fully_monomorphized()` before calling, matching its
/// admission gate); the conversion runs under the same env. Anything the converter
/// cannot ground (`Ty::Unsupported`, nominal types, …) simply fails the renderer's
/// closed grammar downstream — fail-closed, never a guessed key.
pub fn faithful_vtable_key_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> trust_types::Ty {
    let _guard = crate::ty_convert::FaithfulScalarsGuard::enable();
    crate::ty_convert::convert_ty_in_env(tcx, ty::TypingEnv::fully_monomorphized(), ty)
}

/// Trust (vtable slice 18): the bound on how deep [`faithful_key_skeleton`] will recurse.
///
/// A rustc type is a finite tree, so the walk terminates without this — the bound exists
/// so a pathologically nested type produces a REFUSAL (fail-closed, its own tag) instead
/// of a multi-kilobyte identity string in every consumer that carries it.
///
/// It bounds this function's OWN `child` recursion and nothing else. It cannot bound the
/// re-entrant chain through [`faithful_vtable_key_ty`], which starts a fresh conversion
/// at `depth = 0` every trip — see [`KeySkeletonFrame`].
const MAX_KEY_NESTING_DEPTH: u32 = 16;

// ─── THE RE-ENTRANCY CYCLE, and why every bound in the type lowering missed it ───
//
// THE DEFECT (reproduced 2026-09-01 as a SIGBUS — a native stack overflow — in
// `trustc`, on a 13-line crate and on `clean-runtime`).
//
// `faithful_key_skeleton` classifies each node by running the FULL type lowering
// (`faithful_vtable_key_ty` -> `ty_convert::convert_ty_in_env`) and asking whether the
// closed grammar admits the result. `convert_ty_in_env` constructs a FRESH
// `TyLoweringCtx`. Every bound the lowering owns — `MAX_TYPE_LOWERING_DEPTH`,
// `MAX_TYPE_LOWERING_NODES`, `MAX_TYPE_LOWERING_PRODUCED_NODES`, the `adt_stack`
// back-edge guard, the memo cache, the canonical cut set — lives in that context and is
// therefore RESET at the boundary. So the guards were never missing; they were
// DISCARDED, once per trip around a cycle that crosses the boundary:
//
//     convert_ty_inner(dyn Fn(&[V]) -> _)      <- TyKind::Dynamic arm
//       -> faithful_principal_key              <- renders the principal's arguments
//         -> faithful_key_component
//           -> faithful_key_skeleton((&[V],))  <- depth RESET to 0
//             -> faithful_vtable_key_ty
//               -> convert_ty_in_env((&[V],))  <- guard state RESET
//                 -> ... -> V's `dyn Fn(&[V]) -> _` field -> back to the top
//
// A trait object whose principal ARGUMENT is a nominal type that transitively HOLDS that
// same trait object closes the loop. It is an ordinary shape, not a pathological one:
// `clean-runtime` is the shipped instance, and the whole `dyn Fn`/`FnMut`/`FnOnce` family
// over a self-holding value domain has it. Nothing bounded the recursion, so `trustc`
// died of the exact failure class it exists to catch.
//
// WHICH SHAPES ACTUALLY CRASH — measured, because two plausible readings of the trace
// were wrong and each would have mis-sized this fix. (a) The `Fn`-sugar TUPLE around the
// arguments is NOT the escape hatch: `dyn Take<Cycle2>` puts the recursive type in
// argument position bare and still SIGBUSes, so it is the POSITION, not the tuple.
// (b) The associated-type BINDING term reaches this same renderer and is the same edge in
// principle, but no binding-term instance reproduces today. The reason is a property of
// the CUT SET, not of the binding position: `canonical_cut_set` computes cut points over
// the NOMINAL FIELD graph (`nominal_frontier` peels `Ref`/`RawPtr`/`Adt` and does not
// follow a `dyn`'s predicate arguments), so a type whose ONLY cycle runs through a key is
// not a cut point and the fresh walk EXPANDS it — while every binding-term shape found so
// far also carries an ordinary recursive field, which makes it a cut point and reduces
// the fresh walk to a one-node marker. The `Cycle2`/`Guarded` pair in
// `tests/ui/trust/trust_vtable_key_reentrancy_cycle.rs` differ in exactly that one field
// and in exactly whether they crash. Do not read "binding terms are safe" out of that —
// read "the cut set is currently covering them".
//
// AND DO NOT READ "an ordinary recursive field makes a type safe" out of it either,
// which is the reason this guard is not narrowed to the uncut case. There is a SECOND
// way the fresh walk expands a type instead of cutting it, and `ty_convert.rs` documents
// it against `MAX_CANONICAL_CUT_NODES` itself: when cut-point discovery exceeds that
// bound "the cut set is EMPTY and lowering is byte-identical to today's" (see also its
// note R1). An empty cut set cuts nothing, whatever the field graph says, and what is
// left holding the line is precisely the per-context `adt_stack` fail-safe that this
// boundary discards. `clean-runtime` reaches the trait object through
// `IoTaskHandle`/`Arc`/`Mutex`/`Condvar`, a large enough graph for that to be live; the
// re-entered roots measured there are `(io_runtime::IoValue,)` and `io_runtime::IoValue`,
// and which of the two routes applies was NOT isolated.
//
// THE FIX is a guard whose state SURVIVES the boundary — a thread-local stack of the
// types whose skeleton is being rendered right now, on the same shape as
// `ty_convert::record_cut_definition`'s `in_progress` set. Two independent bounds,
// because they catch different things and neither is sufficient alone:
//
//   1. EXACT CYCLE DETECTION (`RefusalShape::SelfReferential`). Re-entering a type
//      already on this thread's stack is refused by name. This is not a truncation and
//      it costs no precision on any terminating input: a path from `X` back to `X` must
//      cross `faithful_principal_key`, because `child` only descends to PROPER subterms
//      of a finite rustc type and a type is not a proper subterm of itself — and every
//      crossing resets `depth`, so the chain is a genuine non-terminating fixpoint. The
//      guard therefore fires ONLY on inputs that would otherwise crash the compiler.
//
//   2. A WELL-FOUNDED FRAME BOUND (`RefusalShape::ReentryBoundExceeded`). Detection
//      alone does not prove termination, because a GENERIC family can re-enter with a
//      NEW type on every trip and never repeat one:
//      `struct S<T>(Box<dyn Fn(&S<Box<T>>)>)` walks `S<u8>`, `S<Box<u8>>`,
//      `S<Box<Box<u8>>>`, … all distinct. `MAX_KEY_SKELETON_FRAMES` is the ranking
//      function that makes the descent well-founded regardless of what the type graph
//      does. It is a STOP, not a refusal, so it carries its OWN tag: a bound that is
//      hit must never be reported as a clean "this type has no key".
//
// SOUNDNESS: both outcomes are the pre-existing fail-closed value. The refusal
// propagates as `Err` out of `faithful_principal_key`, which the extractor's
// `TyKind::Dynamic` arm turns into `principal_key: None` and the THIR producer's
// `trait_object_id` turns into an unsupported body. `principal_key: None` takes the THIN
// spelling in `trust-ir-bridge` (`TrustIrTy::Ptr`), so no identity is minted and no two
// trait objects can be merged. It can only lose a proof, never manufacture one.

/// The bound on SIMULTANEOUSLY ACTIVE [`faithful_key_skeleton`] frames on one thread.
///
/// Sized against the other bound in this file: one skeleton call's own `child` chain is
/// capped at [`MAX_KEY_NESTING_DEPTH`] (16), so 64 frames admit four FULLY nested
/// re-entrant renderings before the stop applies. Nothing in the corpus approaches it —
/// the cycle above is caught by the exact detector on its FIRST repeat, one trip in —
/// so this is the backstop for the non-repeating generic family, and hitting it is a
/// reportable event rather than an expected degradation.
///
/// WHERE A HIT IS OBSERVABLE, exactly, because this is the one bound here that can
/// TRUNCATE rather than refuse and a truncation that reports nothing is the defect this
/// whole change is about. It rides the ordinary refusal-tag channel:
/// `RefusalShape::ReentryBoundExceeded` -> `Ty(dyn {principal arg,assoc binding}: key
/// re-entrancy bound exceeded)` -> the `Err` of `faithful_principal_key`, which the THIR
/// producer propagates as the body's unsupported reason and which lands in the
/// reason-tag histogram under its own name, never pooled with a grammar refusal.
///
/// It is NOT separately observable on the EXTRACTOR side: `ty_convert.rs`'s
/// `TyKind::Dynamic` arm ends in `.ok()`, so every refusal — this one and the eight that
/// predate it — collapses to `principal_key: None` with no reason recorded. That is the
/// pre-existing shape of that call site and this bound does not make it worse, but do
/// not read the tag above as covering the extractor. Giving that side a reason needs a
/// carrier `Ty::Dynamic` does not have; until it does, a bound hit during extraction is
/// countable only as one more `None`.
const MAX_KEY_SKELETON_FRAMES: usize = 64;

thread_local! {
    /// The types whose key skeleton is being rendered on this thread, innermost last.
    ///
    /// Thread-local, like `ty_convert::FAITHFUL_SCALARS` and `DATATYPE_DEFS`, because
    /// rustc runs `mir_built` in parallel and each worker owns its own extraction — and
    /// because the cycle crosses a function boundary (`convert_ty_in_env`) that cannot
    /// carry the state as a parameter without threading a context through the whole
    /// type-lowering API.
    static KEY_SKELETON_FRAMES: std::cell::RefCell<Vec<usize>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

pub(crate) fn in_key_skeleton_frame() -> bool {
    KEY_SKELETON_FRAMES.with(|frames| !frames.borrow().is_empty())
}

/// A lifetime-free identity for an interned rustc type.
///
/// rustc INTERNS `Ty<'tcx>`: one allocation per distinct type, so the address `kind()`
/// hands back is injective over types (equal types share it, distinct types cannot).
/// The `usize` is what lets the in-progress stack live in a `thread_local!` at all — a
/// `Ty<'tcx>` cannot, and the borrow it would need does not exist across the re-entry.
pub(crate) fn interned_ty_identity(ty: ty::Ty<'_>) -> usize {
    std::ptr::from_ref(ty.kind()) as usize
}

/// RAII membership in the in-progress set — see the block comment above.
struct KeySkeletonFrame(usize);

impl KeySkeletonFrame {
    /// Claim `ty`, or say WHY it cannot be claimed. Both refusals are named, distinct,
    /// and reported through the ordinary refusal-tag channel.
    fn enter(ty: ty::Ty<'_>) -> Result<Self, trust_types::RefusalShape> {
        let id = interned_ty_identity(ty);
        KEY_SKELETON_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            if frames.contains(&id) {
                return Err(trust_types::RefusalShape::SelfReferential);
            }
            if frames.len() >= MAX_KEY_SKELETON_FRAMES {
                return Err(trust_types::RefusalShape::ReentryBoundExceeded);
            }
            frames.push(id);
            Ok(KeySkeletonFrame(id))
        })
    }
}

impl Drop for KeySkeletonFrame {
    fn drop(&mut self) {
        // Strictly LIFO: the only constructor is `enter`, the value is never moved out
        // of its frame, and `Drop` runs on unwind as well as on return — so the entry
        // popped here is always this frame's own. Asserted rather than assumed, because
        // a mismatched pop would leave a stale id that refuses a legitimate type
        // forever.
        KEY_SKELETON_FRAMES.with(|frames| {
            let popped = frames.borrow_mut().pop();
            debug_assert_eq!(popped, Some(self.0), "key-skeleton frame stack is not LIFO");
        });
    }
}

/// Trust (vtable slice 18): the `tcx`-level walk that turns ONE rustc type into the
/// renderable skeleton `trust_types::VtableKeyTy`.
///
/// # Why this is the half that needs a `tcx`
///
/// Slice 17 rendered principal arguments and binding terms through
/// `trust_types::Ty::vtable_source_type_key_in_body`, whose closed grammar must refuse
/// `Ty::Adt`: that type's `name` is a GENERICS-ERASED def path, so `Vec<i32>` and
/// `Vec<u64>` share one name and admitting it would re-open the merge slice 17 closed.
/// The def path PLUS recursively rendered generic arguments is injective where the erased
/// name is not — and only a `tcx` holder can walk to the arguments at all. This function
/// supplies the facts; `trust_types::VtableKeyTy::render_in_body` owns the rendering and
/// its injectivity obligation, because this crate is workspace-EXCLUDED (`rustc_private`)
/// and cannot run a unit test.
///
/// # ZERO CHURN, by construction
///
/// The pre-slice-18 renderer is tried FIRST at every node, and anything it spells is
/// wrapped VERBATIM as `VtableKeyTy::Closed`. So every key admitted before this slice is
/// not merely equal to what it was — it is produced by the same unchanged code. Only a
/// type that renderer REFUSES can reach the arms below.
///
/// # Regions
///
/// Lifetime arguments are skipped at EVERY depth, matching slice 17's top-level rule.
/// Regions are erased everywhere else in this pipeline; counting them would manufacture
/// divergences between two spellings of one type.
///
/// # What still refuses
///
/// The `_` arm hands back `closed_grammar_refusal_shape` of the SAME converted type slice
/// 17 classified, so every residual census row (`opaque/param`, `unsized`, `fn-like`)
/// keeps its exact tag and stays countable across the slice boundary. In particular the
/// merged `PRE_MONO_ALIAS` sentinel — one string stamped on EVERY param-bearing
/// projection — is still refused, at every depth: admitting it would key `<T as A>::X`
/// and `<U as B>::Y` to one string, which is the same merge in another costume.
fn faithful_key_skeleton<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    owner: &str,
    depth: u32,
) -> Result<trust_types::VtableKeyTy, trust_types::RefusalShape> {
    use trust_types::{RefusalShape, VtableKeyTy as K};

    // BEFORE the conversion below, which is the re-entrant call: `faithful_vtable_key_ty`
    // starts a FRESH `TyLoweringCtx`, so every bound the lowering owns is reset at that
    // boundary and a `dyn` reachable from `ty` walks straight back here. This frame is
    // the only state that survives it. See the block comment on `MAX_KEY_SKELETON_FRAMES`.
    let _frame = KeySkeletonFrame::enter(ty)?;

    let closed = faithful_vtable_key_ty(tcx, ty);
    if closed.vtable_source_type_key_in_body(owner).is_some() {
        return Ok(K::Closed(closed));
    }
    if depth >= MAX_KEY_NESTING_DEPTH {
        return Err(RefusalShape::TooDeep);
    }
    let child = |t: ty::Ty<'tcx>| faithful_key_skeleton(tcx, t, owner, depth + 1);
    match ty.kind() {
        ty::Adt(def, args) => {
            let mut rendered = Vec::new();
            for arg in args.iter() {
                if arg.as_region().is_some() {
                    continue;
                }
                // A const argument has no canonical spelling in this grammar. REFUSE
                // rather than drop it: dropping would merge `Foo<3>` with `Foo<4>` —
                // the principal's own const args already have this disposition.
                let arg_ty = arg.as_type().ok_or(RefusalShape::NominalConstArg)?;
                rendered.push(child(arg_ty)?);
            }
            Ok(K::Nominal {
                path: sysroot_authenticated_def_path_str(tcx, def.did()),
                args: rendered,
            })
        }
        ty::Tuple(elems) => {
            let mut parts = Vec::with_capacity(elems.len());
            for e in elems.iter() {
                parts.push(child(e)?);
            }
            Ok(K::Tuple(parts))
        }
        ty::Array(elem, len) => {
            let n = len.try_to_target_usize(tcx).ok_or(RefusalShape::SymbolicArrayLen)?;
            Ok(K::Array { elem: Box::new(child(*elem)?), len: u128::from(n) })
        }
        ty::Ref(_, inner, mutability) => {
            Ok(K::Ref { mutable: mutability.is_mut(), inner: Box::new(child(*inner)?) })
        }
        ty::RawPtr(pointee, mutability) => {
            Ok(K::RawPtr { mutable: mutability.is_mut(), pointee: Box::new(child(*pointee)?) })
        }
        _ => Err(trust_types::closed_grammar_refusal_shape(&closed)),
    }
}

/// Trust (vtable slice 18): render ONE type of a trait object's key, faithfully.
///
/// The single entry point for both halves of the key (principal arguments and
/// associated-type binding terms); the caller supplies only the tag PREFIX so the two
/// populations stay separately countable in the reason-tag histogram.
fn faithful_key_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    owner: &str,
    tag_for: fn(trust_types::RefusalShape) -> &'static str,
) -> Result<String, &'static str> {
    faithful_key_skeleton(tcx, ty, owner, 0)
        .and_then(|skeleton| skeleton.render_in_body(owner))
        .map_err(tag_for)
}

/// Trust (vtable slice 17, SOUNDNESS): the ONE renderer of a trait object's FAITHFUL,
/// INJECTIVE principal key — the string EVERY shared trait-object identity must be
/// derived from.
///
/// # The defect this closes
///
/// `Ty::Dynamic { trait_name }` records the principal trait's def path and nothing
/// else, so `dyn Convert<u32>` and `dyn Convert<u64>` render ONE string. Two consumers
/// keyed identities on it:
///   * `trust_ir::stable_vtable_global_name` — one global NAME for two vtables, i.e. an
///     asserted `Load`-equality of two DIFFERENT vtables.
///   * `trust_ir::stable_trait_object_id` -> `FatPtrKind::TraitObject { trait_id }`,
///     which IS the trait object's TYPE IDENTITY. `differential.rs`'s `tys_agree`
///     compares those ids with `Ok(x == y)`, so it returned TRUE for two genuinely
///     different types — a path to a FALSE AGREED, strictly worse than the name merge
///     (a wrong global name is a wrong load; a wrong type identity corrupts the
///     comparison itself).
///
/// The per-body collision tripwire in `trait_object_id` could not catch this **by
/// construction**: it guards two DISTINCT def paths hashing to ONE id (an FNV
/// collision), and erasure is the OPPOSITE direction — two distinct trait objects
/// rendering the SAME def path, which lands in its approve arm. That tripwire is
/// retained (it still guards genuine collisions, which faithful rendering does not
/// eliminate); this function supplies its missing twin.
///
/// # Why FAITHFUL rather than a blanket refusal
///
/// The two designs fail in opposite directions. Erasure fails OPEN and invisibly (two
/// types -> one id -> a false agreement). A rendering drift between the two sides fails
/// VISIBLY (one type -> two ids -> the bodies simply do not agree), costing measurement
/// and never soundness. So the precise option is also the safe one, and a blanket
/// refusal would pay real capability — `dyn Fn(A) -> B` desugars to `Fn<(A,)>`, so every
/// `dyn Fn`/`FnMut`/`FnOnce` would refuse — for a defect that has zero corpus
/// population. See CLAUDE.md v7/D2.
///
/// # Drift is impossible by construction, not by discipline
///
/// This is the SINGLE renderer. Both `tcx`-holding callers — the THIR producer's
/// `trait_object_id` and the extractor's `TyKind::Dynamic` arm — call it; neither
/// re-derives it. The extractor stamps the result into `Ty::Dynamic { principal_key }`,
/// and the MIR-side bridge (which has no `tcx` and must never acquire one) only ever
/// HASHES the string it was handed. `trait_object_id`'s own comment records that a
/// hand-copied second producer of one identity drifted once already; this is that lesson
/// applied one level up.
///
/// # The rendering, and its injectivity obligation
///
/// The obligation is over the TYPE, not the string: two distinct trait objects must
/// never render to one string. So the WHOLE existential predicate list participates —
/// principal path, non-lifetime principal args, associated-type bindings, and auto
/// traits — each through the closed, canonical grammar `vtable_source_type_key`, whose
/// admitted spellings are canonical for the rustc type they came from (so equal
/// renderings imply equal types, which is the soundness direction).
///
/// LIFETIMES ARE EXCLUDED, deliberately: regions are erased everywhere else in this
/// pipeline, so admitting them would manufacture divergences between two spellings of
/// one type — and would refuse `&'a V -> &'a dyn T`, a real shape.
///
/// # Fail-closed BACKSTOP
///
/// The policy is *render faithfully; if it cannot be rendered injectively, refuse*.
/// `None` whenever any component escapes the closed grammar (a param/placeholder/opaque
/// or nominal argument, a const term, a binding whose term is unrenderable) or any
/// rendered component contains `$` (the vtable mint splits at the LAST `$`; asserted
/// here rather than assumed). Falling back to the erased spelling IS the bug.
///
/// # Zero churn on already-minted identities
///
/// An args-free, binding-free, auto-trait-free principal returns `safe_def_path_str`
/// VERBATIM — the function literally returns that string rather than reconstructing it —
/// so every existing `trait_id` and the three shipped slice-3 vtable globals are
/// byte-identical BY CONSTRUCTION.
pub fn faithful_principal_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    preds: &ty::List<ty::PolyExistentialPredicate<'tcx>>,
    owner: &str,
) -> Result<String, &'static str> {
    fn dollar_free(s: String) -> Result<String, &'static str> {
        if s.is_empty() || s.contains('$') {
            Err("Ty(dyn key: '$' or empty in rendered component)")
        } else {
            Ok(s)
        }
    }

    // SYSROOT-AUTHENTICATED, deliberately. The stamp is identity for a real sysroot
    // crate and non-identity only for one IMPERSONATING it, so an impersonating
    // `core::fmt::Debug` can never share an identity with the real one. This is also the
    // spelling the extractor already stamps into `trait_name` and the vtable mint already
    // uses on BOTH sides — so the three shipped slice-3 globals are byte-identical — and
    // adopting it here additionally closes a pre-existing asymmetry: the producer's
    // `trait_object_id` hashed the UNSTAMPED `safe_def_path_str` while the oracle hashed
    // the stamped one. Identity in this corpus, divergent under impersonation.
    // Trust (wave-DNP): a PRINCIPAL-LESS trait object (`dyn Send`, `dyn Send + Sync`) is
    // identified ENTIRELY by its auto-trait set, so it gets an EMPTY base and the existing
    // `+auto` tail does the rest. Two properties make that key injective rather than merely
    // convenient, and both are already pinned by the code below:
    //   * DISJOINT FIRST CHARACTER — a principal-ful key always begins with a def-path
    //     character, and a principal-less one always begins with `+` (the auto tail is
    //     non-empty by the refusal below), so the two families cannot collide;
    //   * the auto set is SORTED and def-path-stamped, so `dyn Send + Sync` and
    //     `dyn Sync + Send` are one key and an impersonating `Send` is not the real one.
    // The `None` branch fails closed on anything that is not purely auto traits: a
    // projection bound without a principal is not constructible (refuse rather than assume),
    // and a `dyn` with neither principal nor autos is not a type.
    let principal = preds.principal();
    let (base, tr) = match principal {
        Some(p) => {
            let tr = p.skip_binder();
            (dollar_free(sysroot_authenticated_def_path_str(tcx, tr.def_id))?, Some(tr))
        }
        None => {
            if preds.projection_bounds().next().is_some() {
                return Err("Ty(dyn no principal: unrenderable auto set)".into());
            }
            if preds.auto_traits().next().is_none() {
                return Err("Ty(dyn no principal: unrenderable auto set)".into());
            }
            (String::new(), None)
        }
    };

    // Principal arguments — NON-LIFETIME only.
    let mut args = Vec::new();
    for arg in tr.iter().flat_map(|t| t.args.iter()) {
        if arg.as_region().is_some() {
            continue;
        }
        // A const argument has no canonical spelling in the closed grammar yet: refuse
        // rather than drop it (dropping would merge `dyn Foo<3>` with `dyn Foo<4>`).
        let arg_ty = arg.as_type().ok_or("Ty(dyn principal arg: const-generic)")?;
        // BODY-SCOPED: a bare `ty::Param` argument (`dyn A<T>`) is renderable — `T` is a
        // single fixed type within one body — but it is NOT body-independent, so the key
        // names the owner. Rendering it with the owner-less renderer would refuse
        // `dyn A<T>` outright; rendering it WITHOUT the owner would merge two bodies'
        // `dyn A<T>` into one `trait_id` for two distinct types. Concrete arguments are
        // body-independent and delegate, so `dyn A<i32>` keeps its exact spelling.
        // Trust (vtable slice 18): a NOMINAL argument now renders too — def path plus
        // recursively rendered arguments, which is injective where `Ty::Adt`'s erased
        // `name` was not. The closed grammar still runs first at every node, so every
        // spelling admitted before this slice is byte-identical.
        let rendered =
            faithful_key_component(tcx, arg_ty, owner, trust_types::principal_arg_refusal_tag_for)?;
        args.push(dollar_free(rendered)?);
    }

    // Associated-type bindings: `dyn Iterator<Item = u32>` and `<Item = u64>` are
    // DIFFERENT TYPES sharing one principal path, so omitting them would leave exactly
    // the merge this function exists to prevent.
    let mut bindings = Vec::new();
    for proj in preds.projection_bounds() {
        let p = proj.skip_binder();
        let name = dollar_free(sysroot_authenticated_def_path_str(tcx, p.def_id))?;
        let term = p.term.as_type().ok_or("Ty(dyn assoc binding: const term)")?;
        // Trust (vtable slice 18): the binding term takes the same faithful nominal
        // rendering as a principal argument — `Item = Vec<i32>` and `Item = Vec<u64>` are
        // different types sharing one principal path AND one binding name, so the term is
        // the only thing that can separate them.
        let term_key =
            faithful_key_component(tcx, term, owner, trust_types::assoc_binding_refusal_tag_for)?;
        bindings.push(format!("{name}={}", dollar_free(term_key)?));
    }
    bindings.sort();

    // Auto traits: `dyn Debug` and `dyn Debug + Send` are different types. Their VTABLES
    // coincide (an auto trait adds no entries), so merging them was harmless for the
    // vtable name — but not for the type identity `tys_agree` compares.
    let mut autos = Vec::new();
    for did in preds.auto_traits() {
        autos.push(dollar_free(sysroot_authenticated_def_path_str(tcx, did))?);
    }
    autos.sort();

    // Trust (wave-DNP): guarded on `principal.is_some()` so the empty-base case can never
    // take the verbatim return (it would yield the empty string).
    if principal.is_some() && args.is_empty() && bindings.is_empty() && autos.is_empty() {
        // The overwhelmingly common `dyn Trait` — returned VERBATIM, so no existing
        // identity can churn.
        return Ok(base);
    }

    let mut out = base;
    if !args.is_empty() {
        out.push('<');
        out.push_str(&args.join(", "));
        out.push('>');
    }
    for b in &bindings {
        out.push_str("+[");
        out.push_str(b);
        out.push(']');
    }
    for a in &autos {
        out.push('+');
        out.push_str(a);
    }
    Ok(out)
}

pub fn extract_function<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> VerifiableFunction {
    extract_function_with_contract_bundle(tcx, body, None)
}

/// Extract executable MIR for the trust-cg backend without verifier-only
/// abstractions.
///
/// Unlike [`extract_function`], this API is a checked, fallible seam. It keeps
/// real derived bodies, requires one-to-one executable control flow, and
/// recursively rejects every TrustIr placeholder before any object emission.
pub fn extract_function_for_codegen<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> Result<VerifiableFunction, CodegenExtractionError> {
    let mut function = extract_function_with_purpose(tcx, body, None, ExtractionPurpose::Codegen);
    validate_codegen_fidelity(tcx, body, &mut function, CodegenTyPolicy::Strict)?;
    Ok(function)
}

/// How [`validate_codegen_fidelity`] judges ADT-typed signatures and locals.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CodegenTyPolicy {
    /// Every ADT is layout-erased for this consumer — the MIR->LIR codegen
    /// lane, whose lowering has no ADT story at all. The historical default.
    Strict,
    /// ADMIT an ADT that carries its FAITHFUL layout facts — an enum marked
    /// `faithful_enum_repr: Some(_)` (extracted under the FaithfulScalarsGuard
    /// with register_enum-eligible structure) or a struct with a concrete
    /// `layout: Some(_)`. The trust-ir upstream lane's policy: the bridge
    /// registers such defs producer-equal (the differential's oracle does so
    /// on every local body), and the converter's pair-enum / recorded-layout
    /// lanes consume them; anything the chain cannot map still refuses
    /// DOWNSTREAM by name — never a miscompile, never a silent admit here.
    AdmitFaithfulAdts,
}

/// [`extract_function_for_codegen`] for the trust-ir UPSTREAM lane: the
/// extraction runs under the [`ty_convert::FaithfulScalarsGuard`] (so
/// isize/usize/char keep their identity and eligible enums carry
/// `faithful_enum_repr` — the exact spellings `lower_mir_compat_to_trust_ir`
/// maps, proven daily by the THIR/MIR differential's oracle side), and the
/// fidelity gate judges ADTs under [`CodegenTyPolicy::AdmitFaithfulAdts`].
/// Every STRUCTURAL fidelity check (block order, statement shapes,
/// terminators) is unchanged.
pub fn extract_function_for_trust_ir_upstream<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> Result<VerifiableFunction, CodegenExtractionError> {
    let _guard = crate::ty_convert::FaithfulScalarsGuard::enable();
    let mut function = extract_function_with_purpose(tcx, body, None, ExtractionPurpose::Codegen);
    validate_codegen_fidelity(tcx, body, &mut function, CodegenTyPolicy::AdmitFaithfulAdts)?;
    Ok(function)
}

/// Extract a VerifiableFunction using an optional typed compiler contract bundle.
///
/// Passing `None` preserves the native fail-closed behavior: only compiler/HIR
/// facts are considered; the legacy source scraper is deleted, so there is no
/// text-recovery fallback of any kind.
pub fn extract_function_with_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> VerifiableFunction {
    extract_function_with_purpose(tcx, body, compiler_contracts, ExtractionPurpose::Verification)
}

/// [`extract_function_with_contract_bundle`], plus the compiler's ELEMENT-SIZE TABLE
/// for the function (ALLOC-STRIDE-ADT-2): a lower bound of rustc's `size_of` for each
/// lowered ADT/tuple/array/datatype key, over every rustc type this extraction lowered
/// to it (see `elem_sizes`). The function is byte-identical to the one
/// [`extract_function_with_contract_bundle`] returns — the table is collected beside
/// it, never in it. Hand it to vcgen with `trust_vcgen::VcgenContext::with_elem_sizes`.
pub fn extract_function_with_contract_bundle_and_elem_sizes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (VerifiableFunction, trust_vcgen::ElemSizeTable) {
    let mut table = trust_vcgen::ElemSizeTable::default();
    let function = extract_function_with_purpose_observed(
        tcx,
        body,
        compiler_contracts,
        ExtractionPurpose::Verification,
        None,
        Some(&mut table),
    );
    (function, table)
}

/// Extract the ordinary verification model and both compiler-owned fact tables.
/// Decimal facts reuse the real-alloc ToString/selected-Self gate, and do not
/// change any serialized function, census or proof-certificate identity.
pub fn extract_function_with_compiler_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (VerifiableFunction, trust_vcgen::ElemSizeTable, trust_vcgen::PrimitiveDecimalStringTable) {
    let (function, sizes) =
        extract_function_with_contract_bundle_and_elem_sizes(tcx, body, compiler_contracts);
    let decimal_strings = primitive_decimal_strings::collect(tcx, body, &function);
    (function, sizes, decimal_strings)
}

fn extract_function_with_purpose<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
    purpose: ExtractionPurpose,
) -> VerifiableFunction {
    extract_function_with_purpose_observed(tcx, body, compiler_contracts, purpose, None, None)
}

fn extract_function_with_purpose_observed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
    purpose: ExtractionPurpose,
    allocation_output: Option<&mut Vec<mir::interpret::AllocId>>,
    elem_sizes_output: Option<&mut trust_vcgen::ElemSizeTable>,
) -> VerifiableFunction {
    // Trust (ALLOC-STRIDE-ADT-2): this extraction's element-size scope, opened
    // before ANY type is lowered. Active only when the caller asked for the table;
    // inactive otherwise, which also suspends an enclosing extraction's recording
    // (the scope saves and restores it).
    let elem_sizes_scope = elem_sizes::ElemSizeScope::begin(elem_sizes_output.is_some());
    // R0: open THIS function's out-of-band datatype-definition scope. Every
    // canonical cut point lowered anywhere below — body locals, blocks, return
    // type, and the contract/signature types lowered by the metadata pass — files
    // its definition here, and the accumulated table is stamped onto the body
    // below. The scope clears on entry and on drop, so one function's table can
    // never inherit another's entry.
    let _datatype_defs = ty_convert::DatatypeDefScope::begin();
    // Trust (2026-09-29): this function's tuple-layout table, scoped exactly like the
    // datatype-definition table above and stamped onto the function below, after the
    // last type lowering this extraction does.
    let _tuple_layouts = tuple_layouts::TupleLayoutScope::begin();
    // Actual AllocIds share identity only inside this extraction. Reserve the
    // scope before metadata/type conversion; nested extraction restores it.
    let _constant_images = ty_convert::faithful_scalars()
        .then(|| constant_image::MemoryImageScope::begin(tcx, body));
    let def_id = body.source.def_id();
    let def_path = safe_def_path_str(tcx, def_id);
    // Trust (vtable slice 17): open the BODY-SCOPED owner scope BEFORE any type is
    // converted (metadata/signature types included), so every `Ty::Dynamic` this
    // extraction produces carries the same owner the THIR producer will use.
    let _owner_scope = ty_convert::OwnerDefPathScope::begin(&def_path);
    let _body_ty_memo = ty_convert::BodyTyMemoScope::begin(tcx);
    let metadata = extract_metadata_with_contract_bundle(tcx, body, compiler_contracts);
    // Trust: Use opt_item_name to avoid panic on closures/synthetic items
    // (e.g. `fmt::builders::{closure#0}`). Fall back to last segment of def_path.
    let name = tcx
        .opt_item_name(def_id)
        .map(|s| s.to_string())
        .unwrap_or_else(|| def_path.rsplit("::").next().unwrap_or(&def_path).to_string());

    // Parse contract bodies into formulas for direct consumption.
    let (mut preconditions, mut postconditions) =
        parse_contract_specs_with_typed(&metadata.contracts, compiler_contracts);

    // Build structured FunctionSpec from contracts.
    let spec = metadata.spec;

    // Build both views of MIR debug names before extraction, then extend them
    // from one shared, HIR-owned parameter recovery.  The extracted local names
    // and the raw assumption-gate multimap must never disagree about a recovered
    // parameter: doing the two recoveries independently lets one side accept a
    // spelling that the other side rejected as ambiguous.
    //
    // When every parameter `1..=arg_count` already carries a MIR debug name and
    // the function has no contract clauses, HIR recovery is a guaranteed no-op
    // (`occupied_locals` contains `1..=arg_count`) and neither contract gate
    // reads `debug_name_locals` or `hir_param_source_names`.
    let mut debug_local_names = build_debug_name_map(body);
    let any_missing_param_name =
        body.arg_count > 0 && (1..=body.arg_count).any(|idx| !debug_local_names.contains_key(&idx));
    let need_hir_param_names = any_missing_param_name || !preconditions.is_empty();
    let hir_param_source_names = (body.arg_count > 0 && need_hir_param_names)
        .then(|| hir_parameter_source_names(tcx, body))
        .flatten();
    let need_debug_multimap = (any_missing_param_name && hir_param_source_names.is_some())
        || !preconditions.is_empty()
        || !postconditions.is_empty();
    let mut debug_name_locals =
        if need_debug_multimap { build_debug_name_multimap(body) } else { FxHashMap::default() };
    if any_missing_param_name {
        if let Some(source_names) = hir_param_source_names.as_deref() {
            merge_recovered_parameter_names(
                &mut debug_local_names,
                &mut debug_name_locals,
                body.arg_count,
                source_names,
            );
        }
    }
    // Trust (identity binding, 2026-10-02): a loop-clause ROOT name binds exactly
    // the local its HIR binding resolved to (`CompilerContractBundle::
    // loop_clause_source_locals`), never a local that merely carries the same debug
    // name. Strip every such spelling from every local, then write each resolved
    // one onto its local; an unresolved name binds nothing, so its clause fails
    // closed.
    if let Some(table) = compiler_contracts.and_then(|bundle| bundle.loop_clause_source_locals.as_ref())
    {
        for (name, target) in table {
            debug_local_names.retain(|_, existing| existing != name);
            if let Some(local) = target {
                debug_local_names.insert(*local, name.clone());
            }
        }
    }

    let mut verifiable_body = extract_body(tcx, body, purpose, &debug_local_names);
    // R0: stamp what the type lowering recorded so far, BEFORE the gates below
    // run — `gate_contract_preconditions` reads the body's own types when
    // preconditions are present, and under markers-everywhere those types are
    // bare markers that mean nothing without this table. It is re-stamped after
    // the gates, since a gate may itself lower a type and add an entry.
    if !preconditions.is_empty() {
        verifiable_body.datatype_defs = ty_convert::collected_datatype_defs();
    }

    // Derived bodies stay intact. An attribute/trait name cannot authorize a
    // synthetic zero-obligation replacement: Hash and Debug execute caller-
    // supplied hasher/writer behavior, and `automatically_derived` is itself
    // source-spellable.

    // The text parser gives ordinary identifiers `Sort::Int`. Restore the
    // source signature's Boolean parameter/return sorts before either body
    // assumptions or modular summaries consume the formulas. This makes
    // `requires(flag)` / `requires(flag == true)` bind the actual Bool local
    // instead of becoming an ungroundable integer atom.
    retype_contract_formulas_for_body(&mut preconditions, &mut postconditions, &verifiable_body);

    // Soundness gate: contract preconditions become BODY hypotheses
    // (`conjoin_live_preconditions`), which is only sound if they bind genuine
    // entry parameters. Shadowed debug names provably transferred a param bound
    // to an unconstrained body local (false PROVE); unsatisfiable predicates
    // would verify vacuously. Gate failure drops the assumption — never the
    // function. Call-site Precondition VCs are generated elsewhere and stay
    // ungated (callers must prove the full predicate).
    // Trust (#14): at low `-Cdebuginfo` the verification body's `var_debug_info`
    // is EMPTY (probe-confirmed: `param_locals=[(1, None)]`,
    // `debug_name_locals={}`), so the NATIVE (span-only, verifier-language)
    // first-class clause lane — `fn f(..) requires x < 10` — cannot bind its
    // parameter through debug names and `gate_contract_preconditions` drops the
    // assumption. Recover the parameter names from the HIR body's exact vector
    // of plain direct bindings, which is debuginfo-independent. This is SOUND:
    // MIR guarantees locals `1..=arg_count` ARE the parameters in declaration
    // order, so naming local `i` by the `i`-th HIR binding names the real entry
    // parameter. Recovery happens ONLY when HIR and MIR parameter counts match
    // and every HIR parameter is a plain binding; each name is then rejected if
    // either debug map already occupies its local or spelling. With empty
    // `var_debug_info` no body local carries a name, so no shadow can exist in
    // the formula namespace (the copy-propagated-shadow false-PROVE hazard
    // requires a *misleading debug entry*, which absent debug info cannot
    // produce). Every present-but-conflicting debug-name case keeps its existing
    // fail-closed shadow gate untouched. The shared recovery above injects every
    // accepted HIR binding into both maps before body extraction.
    // The HIR parameter spellings are the assumption gate's only positive
    // parameter-hood evidence (see that module's header (IV)); reused from the
    // single `hir_parameter_source_names` computation above, so the two can never
    // disagree about which source name a MIR argument carries.
    let skipped = contract_assumption_gate::gate_contract_preconditions(
        &mut preconditions,
        &verifiable_body,
        &debug_name_locals,
        hir_param_source_names.as_deref(),
    );
    contract_assumption_gate::rebind_postcondition_lengths(
        &mut postconditions,
        &verifiable_body,
        &debug_name_locals,
    );
    if !skipped.is_empty() {
        tcx.sess.with_trust_compiler_state::<SessionContractPreconditionsDropped, _>(|state| {
            state.definitions.insert(body.source.def_id());
        });
    }
    for reason in &skipped {
        if first_contract_assumption_warning(tcx, body.source.def_id(), reason) {
            tcx.sess.dcx().span_warn(
                body.span,
                format!(
                    "`#[trust::requires]` on `{name}` is not assumed for body verification: {}",
                    reason.describe()
                ),
            );
        }
    }

    // Share one lazy dense local write-count buffer across both single-definition
    // type-invariant passes below (computed at most once, and not at all when the
    // body has neither discriminant temps nor non-parameter `char` locals).
    let mut shared_write_counts: Option<Vec<u32>> = None;

    // Trust: attach always-true enum-discriminant range invariants so exhaustive
    // `match` arms prove their otherwise-`Unreachable` obligation instead of
    // degrading to runtime-checked. See `enum_discriminant_range_preconditions`.
    preconditions.extend(enum_discriminant_range_preconditions(
        tcx,
        body,
        &verifiable_body,
        &mut shared_write_counts,
    ));

    // Trust: attach the always-true Unicode-scalar-value range invariant for
    // char-typed locals (the char type invariant; see
    // `char_range_preconditions`) — without it the u32 lowering lets the
    // solver pick values above char::MAX (e.g. 268435456) and false-refute
    // arithmetic/allocation guards downstream of `.chars()` loops.
    preconditions.extend(char_range_preconditions(
        body,
        &verifiable_body,
        &mut shared_write_counts,
    ));

    // Trust: attach the always-true integer type-range invariant
    // `MIN_T <= p <= MAX_T` for each integer PARAMETER — without it the param's
    // `Sort::Int` var is unconstrained and the solver false-refutes facts that
    // hold for every in-type value (e.g. `x.saturating_add(y) >= x` needs
    // `y >= 0`). A type tautology, so sound to add unconditionally after the
    // assumption gate (see `integer_param_range_preconditions`). Audit #6.
    preconditions.extend(integer_param_range_preconditions(&verifiable_body));

    // R0: final stamp — a superset of the one taken right after `extract_body`
    // (the accumulator only ever grows inside one scope, except that a CONFLICT
    // removes a name, which is the fail-closed direction). Every bare marker this
    // function's types carry is defined here or nowhere, and "nowhere" is exactly
    // the pre-carrier decline.
    verifiable_body.datatype_defs = ty_convert::take_collected_datatype_defs();

    if let Some(output) = allocation_output {
        *output = constant_image::captured_allocations();
    }
    // Trust (ALLOC-STRIDE-ADT-2): taken after the last type lowering.
    if let Some(output) = elem_sizes_output {
        *output = elem_sizes_scope.take_table();
    }
    VerifiableFunction {
        name,
        def_path,
        span: convert::convert_span(tcx, body.span),
        body: verifiable_body,
        contracts: metadata.contracts,
        preconditions,
        postconditions,
        spec,
        tuple_layouts: tuple_layouts::collected_tuple_layouts(),
    }
}

/// Trust: emit always-true enum-discriminant range invariants as function
/// preconditions. Two consumers benefit: an exhaustive `match` discharges its
/// `otherwise -> Unreachable` obligation statically (the original #24 use), and
/// — #28 — an `e as int` cast and any arithmetic on the result are bounded, so
/// `let d = e as u32; if d >= 1 { d - 1 }` proves instead of false-FAILing.
///
/// For a discriminant temp `_d` assigned exactly once — by
/// `Rvalue::Discriminant(_p)` where `_p` is an enum with valid discriminant tags
/// `{t0, t1, …}` — the fact `_d ∈ {t0, t1, …}` holds wherever `_d` is read (the
/// discriminant of any validly-constructed enum is one of its tags; reading the
/// discriminant of an invalidly-constructed one is already UB upstream). We emit
/// it for *every* such temp, independent of how `_d` is consumed. For an
/// exhaustive switch `check_unreachable` conjoins it into the unreachable block's
/// path condition `_d ∉ targets`, giving `(_d ∈ tags) ∧ (_d ∉ tags)` = UNSAT →
/// proved; a partial match closed with `unreachable_unchecked()` (`targets ⊊
/// tags`) stays SAT → not proved, preserving its genuine UB obligation. For the
/// `e as int` path the same `_d ∈ {tags}` kills the free-i64 cast-overflow model
/// (`_d = -1`) that otherwise false-FAILs the cast and any downstream arithmetic.
///
/// Soundness rests on single-assignment: a global precondition about `_d` is only
/// sound if `_d` never legitimately holds a non-discriminant value, so we require
/// exactly one write to `_d` across the body. Emitting it unconditionally (not
/// only when `_d` drives an `Unreachable`-otherwise switch) is monotone-safe: the
/// fact is always true, so it can only turn a false-FAIL into a PROVE, never an
/// overflow into a false-PROVE. The tag values are discriminant *values*
/// (`discr.val`), matching both the `e as int` cast result and a `match` guard,
/// so this introduces no value-vs-index skew on the read side.
/// Dense per-local textual write counts across `vbody.blocks` (`Assign`,
/// `SetDiscriminant`, `Deinit`, and `Terminator::Call` destinations).
fn local_write_counts(vbody: &VerifiableBody) -> Vec<u32> {
    let mut counts = vec![0u32; vbody.locals.len()];
    let mut bump = |local: usize| {
        if local >= counts.len() {
            counts.resize(local + 1, 0);
        }
        counts[local] = counts[local].saturating_add(1);
    };
    for block in &vbody.blocks {
        for stmt in &block.stmts {
            let written = match stmt {
                Statement::Assign { place, .. } => Some(place.local),
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    Some(place.local)
                }
                _ => None,
            };
            if let Some(local) = written {
                bump(local);
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            bump(dest.local);
        }
    }
    counts
}

fn enum_discriminant_range_preconditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    vbody: &VerifiableBody,
    shared_write_counts: &mut Option<Vec<u32>>,
) -> Vec<Formula> {
    // Resolve each whole-local discriminant temp `_d = Discriminant(src)` to the
    // tag set of `src`'s enum type. Scanning the rustc body (not the lowered
    // `vbody`) lets `Place::ty` resolve `src` through an arbitrary projection
    // chain — `Downcast` / `Field` / `Deref` — so a discriminant read on a
    // *nested* enum payload (e.g. the inner `Result` of `Option<Result<_, _>>`,
    // read as `Discriminant(o.downcast(1).field(0))`) recovers the INNER enum's
    // tags. Using the inner tag set is soundness-critical: emitting the outer
    // enum's (possibly smaller) tag set could exclude a valid inner discriminant
    // and turn a genuinely-reachable block UNSAT — a false-PROVE. rustc local
    // indices coincide with `vbody` local indices, so this map keys join with the
    // `vbody`-derived `d` in the switch loop below.
    let mut discr_tags: FxHashMap<usize, Vec<i128>> = FxHashMap::default();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let mir::StatementKind::Assign((place, mir::Rvalue::Discriminant(src))) =
                &stmt.kind
            else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            if let Some(tags) = place_enum_tags(tcx, body, src) {
                discr_tags.insert(place.local.as_usize(), tags);
            }
        }
    }
    if discr_tags.is_empty() {
        return Vec::new();
    }

    // Single pass over the lowered body: count writes per local so the
    // single-assignment soundness gate below can require exactly one definition
    // of each discriminant temp.
    let write_counts = shared_write_counts.get_or_insert_with(|| local_write_counts(vbody));

    // Emit `_d ∈ {tags}` for every single-assignment discriminant temp, in a
    // deterministic (ascending-local) order. Iterating the temps directly rather
    // than only those feeding an `Unreachable`-otherwise switch extends the
    // invariant to the `e as int` cast / arithmetic path; the exhaustive-
    // match discharge is the subset whose temp also drives such a switch.
    let mut out = Vec::new();
    let mut ds: Vec<usize> = discr_tags.keys().copied().collect();
    ds.sort_unstable();
    for d in ds {
        let tags = &discr_tags[&d];
        if tags.is_empty() {
            continue;
        }
        // Discriminant temps are non-return (0), non-argument (1..=arg_count) locals.
        if d <= vbody.arg_count {
            continue;
        }
        // Sound only if `_d` is never overwritten with a non-discriminant value.
        if write_counts.get(d).copied() != Some(1) {
            continue;
        }
        // Must be integer-sorted to share its SMT var with the cast / switch guard.
        if !matches!(vbody.locals.get(d).map(|l| &l.ty), Some(Ty::Int { .. })) {
            continue;
        }
        let name =
            vbody.locals.get(d).and_then(|l| l.name.clone()).unwrap_or_else(|| format!("_{d}"));
        let eqs: Vec<Formula> = tags
            .iter()
            .map(|&t| {
                Formula::Eq(
                    Box::new(Formula::var(&name, Sort::Int)),
                    Box::new(discriminant_tag_to_formula(t)),
                )
            })
            .collect();
        out.push(match eqs.len() {
            1 => eqs.into_iter().next().unwrap_or(Formula::Bool(true)),
            _ => Formula::Or(eqs),
        });
    }
    out
}

/// Trust: emit the always-true Unicode-scalar-value range invariant for
/// char-typed locals as function preconditions — the exact sibling of
/// [`enum_discriminant_range_preconditions`] for the `char` type invariant.
///
/// Rust guarantees every `char` value is a Unicode scalar value: in
/// `[0, 0x10FFFF]` and outside the surrogate gap `[0xD800, 0xDFFF]`
/// (constructing any other value — e.g. via `char::from_u32_unchecked` — is
/// declared UB, so no defined execution violates it). The lowering models
/// `char` as `u32` (ty_convert: "Char: map to u32"), erasing that invariant;
/// the solver then picks values above `char::MAX` (observed: 268435456) and
/// FALSE-REFUTES arithmetic and allocation guards downstream of `.chars()`
/// loops. Char-ness is recovered from the RUSTC body's local types (the
/// lowered body only shows the u32).
///
/// SOUNDNESS mirrors the discriminant pass: the fact is a universal type
/// invariant (monotone — it deletes only infeasible models; any real
/// violation's witness also satisfies it, so no false-PROVE).
///
/// TWO CLASSES OF LOCAL, two gates:
///   * a PARAMETER (`1..=arg_count`) is bound unconditionally — its rustc type
///     IS `char`, so every value it holds is a Unicode scalar value at entry and
///     after any in-body reassignment (which preserves the type). This is the
///     same argument [`integer_param_range_preconditions`] makes for the integer
///     parameter bound, and it is named by that function's rule so the two facts
///     land on the same SMT var. Parameters were previously skipped on the
///     grounds that a parameter-named precondition would become a call-site
///     PROVE obligation; that is not so on this list — call-site `Precondition`
///     VCs are built from the callee's CONTRACT formulas
///     (`extract_contract_formulas_memo` in `trust_verify`), never from
///     `VerifiableFunction::preconditions` — and the integer parameter bound has
///     shipped on this same list since audit #6.
///   * a NON-parameter local is bound only with EXACTLY ONE textual definition,
///     so every value it holds comes from that one char-producing statement.
fn char_range_preconditions<'tcx>(
    body: &mir::Body<'tcx>,
    vbody: &VerifiableBody,
    shared_write_counts: &mut Option<Vec<u32>>,
) -> Vec<Formula> {
    let mut out = Vec::new();
    for (idx, decl) in body.local_decls.iter_enumerated() {
        if !matches!(decl.ty.kind(), rustc_middle::ty::TyKind::Char) {
            continue;
        }
        let l = idx.as_usize();
        // The return slot carries no entry name to bind.
        if l == 0 {
            continue;
        }
        // A parameter needs no single-definition gate; a body local does (see
        // the doc comment's two classes).
        let is_param = l <= vbody.arg_count;
        if !is_param {
            let counts = shared_write_counts.get_or_insert_with(|| local_write_counts(vbody));
            if counts.get(l).copied() != Some(1) {
                continue;
            }
        }
        // Defensive: the lowered local must be the u32 char lowers to, so the
        // fact shares its SMT var with the arithmetic/comparison reads.
        if !matches!(vbody.locals.get(l).map(|d| &d.ty), Some(Ty::Int { width: 32, signed: false }))
        {
            continue;
        }
        let name =
            vbody.locals.get(l).and_then(|d| d.name.clone()).unwrap_or_else(|| format!("_{l}"));
        // A PARAMETER's fact is named by `integer_param_range_preconditions`'
        // rule — the source name only when UNIQUE across all locals, else the
        // collision-safe `_<index>` — so this bound and that one land on the
        // same var, and a shadowed name can never carry this fact onto a
        // different local (which would be an unsound bound, not merely a
        // disconnected one). Body locals keep their existing spelling.
        let name = if is_param && !local_name_is_unique(&vbody.locals, name.as_str()) {
            format!("_{l}")
        } else {
            name
        };
        let var = || Formula::var(&name, Sort::Int);
        out.push(Formula::And(vec![
            Formula::Ge(Box::new(var()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(var()), Box::new(Formula::Int(0x10FFFF))),
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Ge(Box::new(var()), Box::new(Formula::Int(0xD800))),
                Formula::Le(Box::new(var()), Box::new(Formula::Int(0xDFFF))),
            ]))),
        ]));
    }
    out
}

/// Attach the always-true type-range invariant `MIN_T <= p <= MAX_T` for each
/// integer PARAMETER `p` (locals `1..=arg_count`). A parameter has no in-body
/// definition to bound it, so its lowered `Sort::Int` SMT var is otherwise
/// unconstrained and the solver may pick an OUT-OF-TYPE value (e.g. a "negative"
/// `u32`), FALSELY REFUTING an arithmetic/postcondition fact that holds for every
/// real value of the type (e.g. `x.saturating_add(y) >= x` needs `y >= 0`; a
/// guarded `arr[i]` with `i: usize` needs `i >= 0`). Over-refutation audit #6.
///
/// SOUND unconditionally: the bound is a TAUTOLOGY of the parameter's type — it
/// holds for EVERY value the parameter can take, entry or (for a `mut` param)
/// after any in-body reassignment, since a reassignment preserves the type. So,
/// unlike a value-specific `#[requires]`, it is immune to the shadow/mutation
/// hazards the contract-assumption gate guards against, and is added AFTER that
/// gate (like the char/discriminant range facts). It can only CLOSE a false
/// refutation, never admit a false proof. Capped at width <= 64 (the literal
/// bounds must be i128-representable; wider params get no fact — fail-open to the
/// prior behavior, never mis-bounded).
fn local_name_is_unique(locals: &[trust_types::LocalDecl], target: &str) -> bool {
    let mut seen = false;
    for d in locals {
        if d.name.as_deref() == Some(target) {
            if seen {
                return false;
            }
            seen = true;
        }
    }
    seen
}

fn integer_param_range_preconditions(vbody: &VerifiableBody) -> Vec<Formula> {
    if vbody.arg_count == 0 || vbody.locals.is_empty() {
        return Vec::new();
    }
    // `extract_body` populates `locals[i].index == i` densely, so parameters
    // occupy `locals[1..=arg_count]`. Fall back to scanning `&vbody.locals`
    // only on hand-built test bodies where `locals` is sparse or reordered.
    let dense_params = vbody.locals.get(1..=vbody.arg_count).filter(|slice| {
        slice.iter().enumerate().all(|(offset, decl)| decl.index == offset + 1)
            && vbody.locals.first().is_some_and(|ret| ret.index == 0)
            && vbody.locals.get(vbody.arg_count + 1..).is_none_or(|rest| {
                rest.iter().all(|decl| decl.index < 1 || decl.index > vbody.arg_count)
            })
    });
    let param_slice = dense_params.unwrap_or(&vbody.locals);

    // Build a whole-body name-multiplicity map lazily only when > 2 eligible
    // parameters carry names, avoiding `O(arg_count * locals.len())` rescans on
    // wide signatures while paying zero map overhead on 0..=2-parameter bodies.
    let mut name_counts: Option<FxHashMap<&str, u8>> = None;
    let mut eligible_named_queries = 0usize;
    let mut is_unique_name = |target: &str| -> bool {
        eligible_named_queries += 1;
        if eligible_named_queries <= 2 && name_counts.is_none() {
            return local_name_is_unique(&vbody.locals, target);
        }
        let counts = name_counts.get_or_insert_with(|| {
            let mut map: FxHashMap<&str, u8> =
                FxHashMap::with_capacity_and_hasher(vbody.locals.len(), Default::default());
            for d in &vbody.locals {
                if let Some(n) = d.name.as_deref() {
                    let entry = map.entry(n).or_insert(0);
                    *entry = entry.saturating_add(1);
                }
            }
            map
        });
        counts.get(target).copied() == Some(1)
    };

    let mut out = Vec::new();
    let mut slice_len_facts: Vec<Formula> = Vec::new();
    for decl in param_slice {
        if dense_params.is_none() && (decl.index < 1 || decl.index > vbody.arg_count) {
            continue;
        }
        let Some(name) = decl.name.as_deref() else {
            continue;
        };
        match &decl.ty {
            Ty::Int { width, signed } if *width > 0 && *width <= 64 => {
                // Name the fact EXACTLY as `place_to_var_name` names this local in the
                // body VCs: the source name only when it is UNIQUE across all locals,
                // else the collision-safe `_<index>`.
                let var_name = if is_unique_name(name) {
                    name.to_string()
                } else {
                    format!("_{}", decl.index)
                };
                let (min, max): (i128, i128) = if *signed {
                    (-(1i128 << (*width - 1)), (1i128 << (*width - 1)) - 1)
                } else {
                    (0, (1i128 << *width) - 1)
                };
                let var = || Formula::var(&var_name, Sort::Int);
                out.push(Formula::And(vec![
                    Formula::Ge(Box::new(var()), Box::new(Formula::Int(min))),
                    Formula::Le(Box::new(var()), Box::new(Formula::Int(max))),
                ]));
            }
            Ty::Slice { .. } => {
                let base = if is_unique_name(name) {
                    name.to_string()
                } else {
                    format!("_{}", decl.index)
                };
                slice_len_facts.push(Formula::Ge(
                    Box::new(Formula::var(&format!("{base}__slice_len"), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ));
            }
            Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. }) => {
                let base = if is_unique_name(name) {
                    name.to_string()
                } else {
                    format!("_{}", decl.index)
                };
                slice_len_facts.push(Formula::Ge(
                    Box::new(Formula::var(&format!("{base}__slice_len"), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ));
            }
            _ => {}
        }
    }
    out.extend(slice_len_facts);
    out
}

/// Tag set of the enum a `Discriminant(place)` rvalue reads, or `None` if `place`
/// is not enum-typed. `Place::ty` walks the projection elems (`Downcast` /
/// `Field` / `Deref`), so for a nested-enum payload read this returns the INNER
/// enum's type — exactly the type whose tag the `Discriminant` rvalue observes.
///
/// The returned tags are DECODED (the same boundary as
/// `ty_convert`'s `VariantDef::discriminant`): rustc's `Discr::val` is a raw
/// two's-complement bit pattern at the discriminant type's width, so
/// `Ordering::Less` arrives as `255` and must be read as `-1` before it can be
/// stated about an `i8`-typed discriminant temp. Emitting the RAW set made
/// `_d ∈ {255, 0, 1}` a FALSE fact about a local whose value is `-1` — and,
/// once the matching `SwitchInt` guard is decoded, an UNSAT one, which would
/// turn the `Less` arm vacuous and discharge every obligation on it.
fn place_enum_tags<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: &mir::Place<'tcx>,
) -> Option<Vec<i128>> {
    // Peel a single reference defensively: a by-`&Enum` match lowers to
    // `Discriminant((*r))`, which `Place::ty` already resolves to the enum, but a
    // bare reference source would otherwise be misread.
    let mut ty = place.ty(&body.local_decls, tcx).ty;
    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() {
        if adt_def.is_enum() {
            // FAIL CLOSED on a tag with no `i128` denotation (a `#[repr(u128)]`
            // tag above `i128::MAX`): emitting `val as i128` for it would state
            // a NEGATIVE membership fact about a local that holds a huge
            // unsigned value — a FALSE fact, and exactly the vacuity channel
            // this decode exists to close. No fact at all is the safe answer.
            return adt_def
                .discriminants(tcx)
                .map(|(_, discr)| crate::ty_convert::decode_discr_tag(discr.val, discr.ty, tcx))
                .collect::<Option<Vec<i128>>>();
        }
    }
    None
}

/// Trust: piece #13 step-2 (safe-async data-safety) — whether `place`'s type is
/// (or peels a single reference to) a COROUTINE frame. A `Discriminant` read on a
/// coroutine selects the resume STATE; its `SwitchInt` covers the valid states
/// with an `otherwise -> Unreachable` arm that is genuinely infeasible (the
/// discriminant is always one of the declared states). We recognize this
/// STRUCTURALLY (the source is a coroutine + the switch cases + an unreachable
/// otherwise) rather than via the coroutine LAYOUT query: `coroutine_layout`
/// requires the OPTIMIZED MIR of this very body, so calling it from inside the
/// MIR-optimization pass (`trust_verify`) triggers a query CYCLE (E0391). The
/// state discriminant type is `u32` and the `otherwise -> unreachable` is rustc's
/// own certification that the switch cases are exhaustive over the states, so no
/// tag-set computation is needed — the case set trivially equals the full state
/// set. SOUNDNESS: identical "selector ∈ cases ⇒ otherwise infeasible" reasoning
/// as an enum match; only a coroutine-discriminant switch with an unreachable
/// otherwise is marked, so a genuine `unreachable_unchecked` elsewhere is
/// untouched.
fn place_ty_is_coroutine<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: &mir::Place<'tcx>,
) -> bool {
    let mut ty = place.ty(&body.local_decls, tcx).ty;
    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    matches!(ty.kind(), rustc_middle::ty::TyKind::Coroutine(..))
}

/// Trust (coroutine resume-state contract) — compile-time cross-pin of the
/// reserved coroutine state discriminants against rustc's OWN ABI constants
/// (`rustc_middle::ty::CoroutineArgsExt::{UNRESUMED,RETURNED,POISONED}`).
///
/// The shared recognizer (`trust_types::coroutine_resume_state_contract`)
/// subtracts `trust_types::assumption::COROUTINE_RESERVED_STATE_{RETURNED,
/// POISONED}` from the dispatch `SwitchInt`'s certified case set to obtain the
/// LIVE resume-state set; trust-types cannot depend on rustc, so the values
/// are pinned there and re-derived HERE from the authoritative constants. If
/// rustc ever renumbers the reserved variants this fails the build instead of
/// silently letting a terminal state into a live set (which would discharge
/// the ResumedAfter* sentinels by construction — the exact unsoundness the
/// contract lane exists to prevent).
const _: () = {
    use rustc_middle::ty::CoroutineArgsExt as _;
    type Args<'tcx> = rustc_middle::ty::CoroutineArgs<TyCtxt<'tcx>>;
    assert!(
        Args::UNRESUMED as u128 == trust_types::assumption::COROUTINE_STATE_UNRESUMED,
        "rustc UNRESUMED discriminant drifted from the trust-types pin"
    );
    assert!(
        Args::RETURNED as u128 == trust_types::assumption::COROUTINE_RESERVED_STATE_RETURNED,
        "rustc RETURNED discriminant drifted from the trust-types pin"
    );
    assert!(
        Args::POISONED as u128 == trust_types::assumption::COROUTINE_RESERVED_STATE_POISONED,
        "rustc POISONED discriminant drifted from the trust-types pin"
    );
};

/// Render an already-DECODED enum tag (see [`place_enum_tags`]) as the constant
/// term of the `_d ∈ {tags}` invariant.
///
/// The tags reaching here are mathematical integers, not raw bit patterns, so
/// this is a plain `Formula::Int` — byte-identical to what the typed
/// `SwitchInt`-label decode (`trust_vcgen::switch_label_to_formula`) produces
/// for the matching arm, which is what lets the two cancel for an exhaustive
/// match regardless of the discriminant's sign.
fn discriminant_tag_to_formula(value: i128) -> Formula {
    Formula::Int(value)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExtractionPurpose {
    Verification,
    Codegen,
}

/// Extract trust-related metadata for a local MIR body.
///
/// This is a sidecar API for issue #10: it keeps the existing `VerifiableFunction`
/// shape intact while making trust annotations explicit and independently testable.
/// Like `extract_function`, this native path does not use compatibility source
/// scraping when compiler contract facts are unavailable.
#[cfg(test)]
pub(crate) fn extract_metadata<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> TrustMetadata {
    extract_metadata_with_contract_bundle(tcx, body, None)
}

fn extract_metadata_with_contract_bundle<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> TrustMetadata {
    let def_id = body.source.def_id();
    let (contracts, contract_extraction) = extract_contracts(tcx, def_id, compiler_contracts);
    // Proof items come exclusively from the compiler-owned contract bundle
    // (native syntax, e.g. `TrustProofItemSource::NativeHarness`). The legacy
    // `#[kani::proof]` / `#[kani::proof_for_contract]` HIR-attribute import was
    // deleted in the R2 deletion wave (D-B).
    let proof_items =
        compiler_contracts.map(|bundle| bundle.proof_items.clone()).unwrap_or_default();
    // Build structured FunctionSpec from contracts.
    let spec = build_function_spec(&contracts);
    TrustMetadata {
        contracts,
        proof_items,
        trust_annotations: extract_trust_annotations(tcx, def_id),
        spec,
        contract_extraction,
    }
}

/// Trust: Safely get the span of an attribute. Returns None for parsed
/// built-in attributes that have no meaningful span (e.g., #[inline]).
/// Only `Tool`/`DeriveHelper` (custom/tool) attributes and a few known
/// `Parsed` variants carry a usable span; all others return None instead of
/// panicking.
fn safe_attr_span(attr: &rustc_attr_ir::Attribute) -> Option<rustc_span::Span> {
    match attr {
        // Custom / tool attributes always have a span.
        rustc_attr_ir::Attribute::Tool(item) | rustc_attr_ir::Attribute::DeriveHelper(item) => {
            Some(item.span)
        }
        // Known Parsed variants with spans (mirrors AttributeExt::span).
        rustc_attr_ir::Attribute::Parsed(AttributeKind::DocComment { span, .. }) => Some(*span),
        rustc_attr_ir::Attribute::Parsed(AttributeKind::Deprecated { span, .. }) => Some(*span),
        // All other Parsed attributes don't have a reliably accessible span.
        rustc_attr_ir::Attribute::Parsed(_) => None,
    }
}

fn extract_contracts(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (Vec<Contract>, ContractExtractionReport) {
    if let Some(bundle) = compiler_contracts {
        if !bundle.contracts.is_empty() {
            if let Some((span, name, collision)) = def_id
                .as_local()
                .and_then(|local_def_id| first_synthetic_contract_parameter(tcx, local_def_id))
            {
                return reject_contracts_for_synthetic_parameter(tcx, span, &name, collision);
            }
            return (
                bundle.contracts.clone(),
                ContractExtractionReport {
                    source: ContractExtractionSource::CompilerContractBundle,
                    source_scraping_used: false,
                    diagnostics: vec![],
                },
            );
        }
    }

    let Some(local_def_id) = def_id.as_local() else {
        return (
            vec![],
            ContractExtractionReport {
                source: ContractExtractionSource::Unavailable,
                source_scraping_used: false,
                diagnostics: vec![
                    "contract extraction unavailable for non-local DefId; source scraping disabled"
                        .to_string(),
                ],
            },
        );
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();
    // Trust (CONTRACT-NS-1): the first scraped body that carries a compiler-internal
    // contract marker, and where. See `reject_scraped_contract_with_compiler_marker`.
    let mut forged_marker: Option<(rustc_span::Span, &'static str)> = None;
    let contracts: Vec<_> = tcx
        .hir_attrs(hir_id)
        .iter()
        .filter_map(|attr| {
            // Trust (CONTRACT-NS-1): the WHOLE path decides, not its last segment.
            let kind = contract_kind_from_attr(attr)?;
            let span = attr.value_span().or_else(|| safe_attr_span(attr))?;
            let body = attr
                .value_str()
                .map(|value| value.to_string())
                .or_else(|| {
                    safe_attr_span(attr).and_then(|s| {
                        source_map
                            .span_to_snippet(s)
                            .ok()
                            .map(|snippet| contract_body_from_attr_snippet(&snippet))
                    })
                })
                .unwrap_or_default();
            if forged_marker.is_none() {
                forged_marker =
                    trust_types::trust_attr_namespace::compiler_contract_marker_in(&body)
                        .map(|marker| (span, marker));
            }

            Some(Contract { kind, span: convert::convert_span(tcx, span), body })
        })
        .collect();

    // Trust (CONTRACT-NS-1): the compiler's markers are honored only on
    // `bundle.contracts`, which the compiler mints (`convert_trust_contract_predicate`)
    // and which returned above. Text scraped from source never carries one.
    if let Some((span, marker)) = forged_marker {
        return reject_scraped_contract_with_compiler_marker(tcx, def_id, span, marker);
    }

    if !contracts.is_empty() {
        if let Some((span, name, collision)) = first_synthetic_contract_parameter(tcx, local_def_id)
        {
            return reject_contracts_for_synthetic_parameter(tcx, span, &name, collision);
        }
        return (
            contracts,
            ContractExtractionReport {
                source: ContractExtractionSource::RustcHirAttributes,
                source_scraping_used: false,
                diagnostics: vec![],
            },
        );
    }

    // R-U §1.2-5: the legacy compat/debug source-scraping fallback is deleted.
    // When neither a compiler bundle nor HIR attributes provide contract facts,
    // extraction fails closed: no contracts, an explicit diagnostic, never a
    // silently recovered spec.
    (
        vec![],
        ContractExtractionReport {
            source: ContractExtractionSource::Unavailable,
            source_scraping_used: false,
            diagnostics: vec![
                "native contract facts unavailable; compatibility source scraping disabled"
                    .to_string(),
            ],
        },
    )
}

/// Find a source parameter whose name aliases a Formula leaf minted by Trust.
///
/// This mirrors the compiler query's recursive parameter-pattern gate.  The
/// extractor must repeat the check because `extract_function(tcx, body)` and
/// the HIR-attribute compatibility seam can run with `compiler_contracts ==
/// None`; trusting those attributes without this guard would bypass the query
/// entirely.  Return only the first collision: one hard error is enough to
/// make the definition unavailable, and no partial contract bundle survives.
fn first_synthetic_contract_parameter(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_span::def_id::LocalDefId,
) -> Option<(rustc_span::Span, String, trust_types::SourceContractSyntheticNameCollision)> {
    struct Collector {
        found:
            Option<(rustc_span::Span, String, trust_types::SourceContractSyntheticNameCollision)>,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Collector {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if self.found.is_none() {
                if let rustc_hir::PatKind::Binding(_, canonical_id, ident, _) = pat.kind {
                    if canonical_id == pat.hir_id {
                        if let Some(collision) =
                            trust_types::source_contract_synthetic_name_collision(
                                ident.name.as_str(),
                            )
                        {
                            self.found = Some((pat.span, ident.name.to_string(), collision));
                        }
                    }
                }
            }
            rustc_hir::intravisit::walk_pat(self, pat);
        }
    }

    let body = tcx.hir_maybe_body_owned_by(local_def_id)?;
    let mut collector = Collector { found: None };
    use rustc_hir::intravisit::Visitor as _;
    for param in body.params {
        collector.visit_pat(param.pat);
    }
    collector.found
}

fn reject_contracts_for_synthetic_parameter(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
    name: &str,
    collision: trust_types::SourceContractSyntheticNameCollision,
) -> (Vec<Contract>, ContractExtractionReport) {
    let namespace = match collision {
        trust_types::SourceContractSyntheticNameCollision::ReturnPlace => "return-place",
        trust_types::SourceContractSyntheticNameCollision::OldValue => "pre-state",
        trust_types::SourceContractSyntheticNameCollision::PositionalPlace => {
            "positional MIR-place"
        }
        trust_types::SourceContractSyntheticNameCollision::PredicateSymbol => "predicate-symbol",
        trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata => {
            "generated Formula metadata"
        }
    };
    let diagnostic = format!(
        "parameter `{name}` collides with the source-contract synthetic {namespace} namespace"
    );
    // The canonical `trust_contracts` query normally emitted the same class of
    // hard error first.  Avoid duplicate noise when it did; when extraction is
    // entered directly with no bundle, this is the load-bearing fail-closed
    // diagnostic that prevents a dropped caller requirement from compiling.
    if tcx.dcx().has_errors().is_none() {
        tcx.dcx().span_err(span, diagnostic.clone());
    }
    (
        Vec::new(),
        ContractExtractionReport {
            source: ContractExtractionSource::Unavailable,
            source_scraping_used: false,
            diagnostics: vec![diagnostic],
        },
    )
}

fn extract_trust_annotations(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<TrustAnnotation> {
    let Some(local_def_id) = def_id.as_local() else {
        return vec![];
    };

    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    let source_map = tcx.sess.source_map();

    tcx.hir_attrs(hir_id)
        .iter()
        .flat_map(|attr| {
            if matches!(attr, rustc_attr_ir::Attribute::Parsed(_)) {
                return vec![];
            }
            let span = match safe_attr_span(attr) {
                Some(s) => s,
                None => return vec![],
            };
            source_map
                .span_to_snippet(span)
                .ok()
                .map(|snippet| {
                    // Trust (T9 contract-panic): a malformed/empty
                    // `contract_panic` payload is a HARD extraction error, not a
                    // silent drop — an annotation that can never match a panic
                    // message must not vanish while the user believes their
                    // intentional-panic contract is recorded. (rustc dedups the
                    // byte-identical diagnostic if this extraction runs twice
                    // for the same def.)
                    for reason in contract_panic_extraction_errors(&snippet) {
                        tcx.sess.dcx().span_err(span, reason);
                    }
                    trust_annotations_from_attr_snippet(&snippet)
                        .into_iter()
                        .map(|(kind, body)| TrustAnnotation {
                            kind,
                            span: convert::convert_span(tcx, span),
                            body,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        })
        .collect()
}

/// Trust (T9 contract-panic): the `contract_panic(message_contains = "...")`
/// payloads declared on `def_id`, for the compiler's verify pass to thread to
/// the trust-vcgen panic-call mint sites through its owner-bound `VcgenContext`.
/// Reuses [`extract_trust_annotations`] — the SAME parser the metadata path
/// uses — so a payload can never differ between the recorded annotation and
/// the one the vcgen matcher sees. Malformed payloads have already been
/// reported as hard errors inside `extract_trust_annotations`; they extract to
/// nothing here (fail-closed: no marker is ever stamped from a broken payload).
#[must_use]
pub fn extract_contract_panic_annotations(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<String> {
    use rustc_hir::def::DefKind;
    let contract_bodies = |did: DefId| -> Vec<String> {
        extract_trust_annotations(tcx, did)
            .into_iter()
            .filter(|a| a.kind == TrustAnnotationKind::ContractPanic)
            .map(|a| a.body)
            .collect::<Vec<_>>()
    };
    let mut out = contract_bodies(def_id);
    // A `#[trust::contract_panic(message_contains = "...")]` on a fn documents an intentional
    // panic for the WHOLE fn body — including panics raised inside its nested closures /
    // coroutines / const-blocks, each of which is a DISTINCT child `def_id`. But
    // `extract_trust_annotations` reads attributes on `def_id` alone, so a nested body would
    // MISS its enclosing fn's contract and the author's declared panic would re-refute — an
    // asymmetry vs `item_has_trust_skip_attr`, which walks to the crate root. Walk ancestors
    // while the current def is a nested body, folding in each enclosing scope's contract_panic
    // bodies up to and including the enclosing fn.
    //
    // SOUNDNESS: `contract_panic` is MESSAGE-MATCHED (`message_contains`). Inheriting it excuses
    // ONLY a nested-body panic whose message matches the declared string — exactly the author's
    // stated intent for that fn's implementation; a differently-messaged panic in the closure
    // still refutes. So this adds no power beyond the message match the mechanism already trusts.
    let mut cur = def_id;
    while matches!(
        tcx.def_kind(cur),
        DefKind::Closure
           
            | DefKind::AnonConst
            | DefKind::SyntheticCoroutineBody
    ) {
        let Some(parent) = tcx.opt_parent(cur) else { break };
        out.extend(contract_bodies(parent));
        cur = parent;
    }
    out
}

/// Trust (CONTRACT-NS-1, 2026-10-03): the contract an HIR attribute states, read from
/// its WHOLE path: only `trust::<contract name>` is one
/// ([`trust_types::trust_attr_namespace::contract_kind_of_attr_path`] holds the rule
/// and its unit tests).
///
/// This replaced a match on `attr.path().last()` alone, which made any tool's
/// attribute a Trust contract: `#[clippy::requires = ".."]` (clippy is an
/// always-registered tool, so it compiles silently) was assumed at function entry and
/// its overflow check elided as kernel-certified, while nothing charged a caller for
/// it. A parsed built-in attribute has no symbol path; `path()` answers `[doc]` for
/// it, which is not a contract either.
fn contract_kind_from_attr(attr: &rustc_attr_ir::Attribute) -> Option<ContractKind> {
    if matches!(attr, rustc_attr_ir::Attribute::Parsed(_)) {
        return None;
    }
    let path = attr.path();
    if let [first, second] = path.as_slice() {
        trust_types::trust_attr_namespace::contract_kind_of_attr_path(&[
            first.as_str(),
            second.as_str(),
        ])
    } else {
        None
    }
}

/// Trust (CONTRACT-NS-1): the definitions whose scraped contract text carried a
/// compiler-internal contract marker and were refused for it. One MIR body is
/// extracted at several verifier seams, and compiletest disables the diagnostic
/// engine's deduplication, so the hard error is owned here: once per definition per
/// Session (see [`SessionContractAssumptionWarnings`] for why Session storage).
#[derive(Default)]
struct SessionForgedContractMarkerErrors {
    emitted: FxHashSet<DefId>,
}

/// Trust (CONTRACT-NS-1): refuse a contract read from an attribute's SOURCE text that
/// carries a compiler-internal contract marker. `__trust_lowered_compiler_contract__:`
/// is minted only by the compiler's own contract query on a predicate it has already
/// lowered and typed (`convert_trust_contract_predicate`), and every consumer that
/// sees it lowers the rest as a compiler-typed formula
/// (`normalized_contract_spec_body`, `verifier_api`'s contract lowering). In scraped
/// text it is a forgery: honoring it turned
/// `#[trust::trust_requires = "__trust_lowered_compiler_contract__:x < 100"]` into an
/// assumed, typed precondition. A hard error at the attribute, and no contracts for
/// the definition (the same shape as [`reject_contracts_for_synthetic_parameter`]),
/// so the body is verified with nothing assumed.
fn reject_scraped_contract_with_compiler_marker(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    span: rustc_span::Span,
    marker: &str,
) -> (Vec<Contract>, ContractExtractionReport) {
    let diagnostic = format!(
        "Trust: contract attribute text carries the compiler-internal marker `{marker}`, which \
         only the compiler's own contract lowering mints; a contract read from source is never \
         pre-lowered"
    );
    let first =
        tcx.sess.with_trust_compiler_state::<SessionForgedContractMarkerErrors, _>(|state| {
            state.emitted.insert(def_id)
        });
    if first {
        tcx.dcx().span_err(span, diagnostic.clone());
    }
    (
        Vec::new(),
        ContractExtractionReport {
            source: ContractExtractionSource::Unavailable,
            source_scraping_used: false,
            diagnostics: vec![diagnostic],
        },
    )
}

fn contract_body_from_attr_snippet(snippet: &str) -> String {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    if let Some(open_idx) = body.find('(') {
        if let Some(close_idx) = body.rfind(')') {
            if close_idx > open_idx {
                return body[open_idx + 1..close_idx].trim().to_string();
            }
        }
    }

    if let Some(eq_idx) = body.find('=') {
        return body[eq_idx + 1..].trim().trim_matches('"').to_string();
    }

    String::new()
}

fn normalized_contract_spec_body(kind: ContractKind, body: &str) -> Option<String> {
    let body = strip_string_literal(body);
    let body = body.trim();
    let body = body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap_or(body);
    if body.is_empty() {
        return None;
    }

    match kind {
        ContractKind::Ensures => {
            Some(normalize_ensures_closure_body(body).unwrap_or_else(|| body.to_string()))
        }
        _ => Some(body.to_string()),
    }
}

fn build_function_spec(contracts: &[Contract]) -> trust_types::FunctionSpec {
    let mut spec = trust_types::FunctionSpec::default();
    for contract in contracts {
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            continue;
        };
        match contract.kind {
            ContractKind::Requires => spec.requires.push(body),
            ContractKind::Ensures => spec.ensures.push(body),
            ContractKind::Invariant | ContractKind::LoopInvariant => spec.invariants.push(body),
            ContractKind::Decreases | ContractKind::TypeRefinement | ContractKind::Modifies => {}
            _ => {}
        }
    }
    spec
}

fn normalize_ensures_closure_body(body: &str) -> Option<String> {
    let mut rest = body.trim();
    if let Some(stripped) = rest.strip_prefix("move") {
        rest = stripped.trim_start();
    }
    if !rest.starts_with('|') {
        return None;
    }

    let after_open = &rest[1..];
    let close_idx = after_open.find('|')?;
    let arg_spec = after_open[..close_idx].trim();
    if arg_spec.is_empty() || arg_spec.contains(',') {
        return None;
    }

    let arg_name = arg_spec.split(':').next()?.trim();
    if arg_name.is_empty() || !arg_name.chars().all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return None;
    }

    let mut expr = after_open[close_idx + 1..].trim();
    if let Some(block_expr) = strip_single_expr_block(expr) {
        expr = block_expr;
    }
    if expr.is_empty() {
        return None;
    }

    let expr = replace_deref_ident(expr, arg_name, "result");
    Some(replace_ident(expr.as_str(), arg_name, "result"))
}

fn strip_single_expr_block(expr: &str) -> Option<&str> {
    let expr = expr.trim();
    let inner = expr.strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.is_empty() || inner.contains(';') {
        return None;
    }
    Some(inner)
}

fn replace_deref_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes[i] == b'*' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if bytes.get(j..j + ident_bytes.len()) == Some(ident_bytes)
                && is_ident_start_boundary(expr, j)
                && is_ident_end_boundary(expr, j + ident_bytes.len())
            {
                out.push_str(replacement);
                i = j + ident_bytes.len();
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn replace_ident(expr: &str, ident: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(expr.len());
    let bytes = expr.as_bytes();
    let ident_bytes = ident.as_bytes();
    let mut i = 0usize;

    while i < bytes.len() {
        if bytes.get(i..i + ident_bytes.len()) == Some(ident_bytes)
            && is_ident_start_boundary(expr, i)
            && is_ident_end_boundary(expr, i + ident_bytes.len())
        {
            out.push_str(replacement);
            i += ident_bytes.len();
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn is_ident_start_boundary(text: &str, start: usize) -> bool {
    start == 0 || !is_ident_char(text.as_bytes()[start - 1])
}

fn is_ident_end_boundary(text: &str, end: usize) -> bool {
    end == text.len() || !is_ident_char(text.as_bytes()[end])
}

fn is_ident_char(b: u8) -> bool {
    (b as char).is_ascii_alphanumeric() || b == b'_'
}

fn trust_annotations_from_attr_snippet(snippet: &str) -> Vec<(TrustAnnotationKind, String)> {
    let mut body = snippet.trim();

    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }

    trust_annotations_from_attr_body(body)
}

fn trust_annotations_from_attr_body(body: &str) -> Vec<(TrustAnnotationKind, String)> {
    let body = body.trim();

    if let Some(rest) = body.strip_prefix("trust(").and_then(|s| s.strip_suffix(')')) {
        return split_trust_annotation_items(rest)
            .into_iter()
            .flat_map(trust_annotation_from_item)
            .collect();
    }

    trust_annotation_from_item(body)
}

fn split_trust_annotation_items(body: &str) -> Vec<&str> {
    let mut items = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escape = false;

    for (idx, ch) in body.char_indices() {
        if in_string {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                items.push(body[start..idx].trim());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    let tail = body[start..].trim();
    if !tail.is_empty() {
        items.push(tail);
    }

    items
}

fn trust_annotation_from_item(item: &str) -> Vec<(TrustAnnotationKind, String)> {
    let item = item.trim();
    if item.is_empty() {
        return vec![];
    }

    match item {
        "boundary" | "trust_boundary" => {
            vec![(TrustAnnotationKind::Boundary, String::new())]
        }
        "model" => vec![(TrustAnnotationKind::Model, String::new())],
        _ => {
            if let Some(body) = trust_assumption_body(item) {
                vec![(TrustAnnotationKind::Assumption, body)]
            } else if let Some(Ok(payload)) = trust_contract_panic_body(item) {
                // Trust (T9 contract-panic): only the WELL-FORMED payload
                // extracts here. The malformed case (`Some(Err(..))`) is NOT a
                // silent drop — `contract_panic_extraction_errors` re-walks the
                // same items at the tcx-bearing extraction site and emits a hard
                // compile error (the unknown-item drop below is the anti-pattern
                // for a recognized-but-broken contract annotation).
                vec![(TrustAnnotationKind::ContractPanic, payload)]
            } else {
                vec![]
            }
        }
    }
}

/// Trust (T9 contract-panic): parse one `contract_panic` annotation item.
///
/// Returns:
///   * `None` — the item is not a `contract_panic` item at all (callers fall
///     through to the unknown-item handling);
///   * `Some(Ok(payload))` — well-formed
///     `contract_panic(message_contains = "<non-empty>")`, payload extracted;
///   * `Some(Err(reason))` — the item IS a `contract_panic` annotation but its
///     payload is malformed or empty. This MUST surface as an extraction ERROR
///     (never a silent drop): a contract-panic annotation that parses to
///     nothing could never match a panic message, and silently dropping it
///     would leave the user believing their intentional-panic contract is
///     recorded when it is not.
///
/// Accepted spellings mirror the sibling arms (`assume`/`trust_assume`) plus
/// the `#[trust::contract_panic(...)]` tool-attribute path form, whose snippet
/// reaches this parser as a single `trust::contract_panic(...)` item.
fn trust_contract_panic_body(item: &str) -> Option<Result<String, String>> {
    let item = item.trim();
    let rest = item
        .strip_prefix("trust::contract_panic")
        .or_else(|| item.strip_prefix("trust_contract_panic"))
        .or_else(|| item.strip_prefix("contract_panic"))?;
    // Reject a mere identifier-prefix collision (e.g. `contract_panicky`).
    if rest.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }

    let malformed = |detail: &str| {
        Some(Err(format!(
            "malformed contract_panic annotation `{item}`: {detail}; expected \
             contract_panic(message_contains = \"<non-empty substring of the panic message>\")"
        )))
    };

    let rest = rest.trim();
    let Some(inner) = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return malformed("missing `(message_contains = \"...\")` payload");
    };
    let inner = inner.trim();
    let Some(value) = inner.strip_prefix("message_contains") else {
        return malformed("payload must be `message_contains = \"...\"`");
    };
    let value = value.trim_start();
    let Some(value) = value.strip_prefix('=') else {
        return malformed("expected `=` after `message_contains`");
    };
    let value = value.trim();
    // The payload must be an explicit non-empty string literal: an unquoted or
    // empty payload matches nothing (or, worse, everything a future laxer
    // matcher might accept) and is rejected fail-closed.
    let Some(payload) = value.strip_prefix('"').and_then(|s| s.strip_suffix('"')) else {
        return malformed("`message_contains` value must be a double-quoted string literal");
    };
    if payload.trim().is_empty() {
        return malformed("`message_contains` payload must be a non-empty substring");
    }
    Some(Ok(payload.to_string()))
}

/// Trust (T9 contract-panic): the malformed-`contract_panic` diagnostics for one
/// attribute snippet. Mirrors the `trust_annotations_from_attr_snippet` →
/// `trust_annotations_from_attr_body` → item traversal exactly (same `#[..]`
/// strip, same `trust(...)` unwrap, same depth/string-aware item split), and
/// shares the single item recognizer `trust_contract_panic_body`, so the "is
/// this a contract_panic item?" judgment can never drift between the extractor
/// and this error walk. Returns one human-readable reason per malformed item.
fn contract_panic_extraction_errors(snippet: &str) -> Vec<String> {
    let mut body = snippet.trim();
    if let Some(stripped) = body.strip_prefix("#[").and_then(|s| s.strip_suffix(']')) {
        body = stripped.trim();
    }
    let items: Vec<&str> =
        if let Some(rest) = body.strip_prefix("trust(").and_then(|s| s.strip_suffix(')')) {
            split_trust_annotation_items(rest)
        } else {
            vec![body]
        };
    items
        .into_iter()
        .filter_map(|item| match trust_contract_panic_body(item) {
            Some(Err(reason)) => Some(reason),
            _ => None,
        })
        .collect()
}

fn trust_assumption_body(item: &str) -> Option<String> {
    let item = item.trim();

    if let Some(rest) = item.strip_prefix("assume").or_else(|| item.strip_prefix("trust_assume")) {
        let rest = rest.trim();
        if rest.is_empty() {
            return Some(String::new());
        }

        if let Some(rest) = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            return Some(strip_string_literal(rest.trim()));
        }

        if let Some(rest) = rest.strip_prefix('=') {
            return Some(strip_string_literal(rest.trim()));
        }
    }

    None
}

fn strip_string_literal(text: &str) -> String {
    let trimmed = text.trim();
    trimmed.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(trimmed).to_string()
}

/// Parse contract bodies into precondition and postcondition formulas.
///
/// Uses `trust_types::parse_spec_expr` to convert textual contract bodies from
/// `#[requires("expr")]` and `#[ensures("expr")]` attributes into `Formula` values.
/// An unparseable `requires` is represented by `false`: dropping a declared
/// caller obligation would be fail-open.  Unparseable `ensures` remains
/// withheld because assuming a malformed guarantee would also be unsound.
#[cfg(test)]
fn parse_contract_specs(contracts: &[Contract]) -> (Vec<Formula>, Vec<Formula>) {
    parse_contract_specs_with_typed(contracts, None)
}

fn parse_contract_specs_with_typed(
    contracts: &[Contract],
    compiler_contracts: Option<&CompilerContractBundle>,
) -> (Vec<Formula>, Vec<Formula>) {
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();

    for (index, contract) in contracts.iter().enumerate() {
        let typed = compiler_contracts.and_then(|bundle| {
            let has_typed_row = bundle
                .typed_propositions
                .iter()
                .any(|proposition| proposition.source_contract_index == index);
            match bundle.typed_proposition(index, contract) {
                Some(proposition) => Some(Ok(proposition.formula.clone())),
                None if has_typed_row => Some(Err(())),
                None => None,
            }
        });
        if let Some(typed) = typed {
            match (contract.kind, typed) {
                (ContractKind::Requires, Ok(formula)) => preconditions.push(formula),
                (ContractKind::Ensures, Ok(formula)) => postconditions.push(formula),
                (ContractKind::Requires, Err(())) => preconditions.push(Formula::Bool(false)),
                (ContractKind::Ensures, Err(())) => {}
                _ => {}
            }
            continue;
        }
        let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) else {
            if contract.kind == ContractKind::Requires {
                preconditions.push(Formula::Bool(false));
            }
            continue;
        };
        let Some(formula) = trust_types::parse_spec_expr(&body) else {
            if contract.kind == ContractKind::Requires {
                preconditions.push(Formula::Bool(false));
            }
            continue;
        };
        match contract.kind {
            ContractKind::Requires => preconditions.push(formula),
            ContractKind::Ensures => postconditions.push(formula),
            ContractKind::Invariant | ContractKind::Decreases => {}
            _ => {}
        }
    }

    (preconditions, postconditions)
}

fn source_contract_sort_for_ty(ty: &Ty) -> Sort {
    // A float PARAMETER must restore to its IEEE sort, not the `Int` default: the
    // text parser's `coerce_float_comparison_operands` sorts `s <= 1.0e30` at f64,
    // but `retype_contract_formulas_for_body` then re-sorts every var whose name is
    // a parameter — so a BARE f64 param `s` (a3d-geom's `scale(self, s)`, the
    // `fov_y`/`near`/`far` of the projection builders) would be clobbered back to
    // `Int`, breaking the assumption-gate witness (`eval_float` no longer fires, so
    // the all-zeros model is not found and the whole magnitude precondition is
    // dropped). A FIELD var (`self.0`) is unaffected either way — its name is not a
    // parameter name, so it is never in this environment and keeps its parsed sort.
    match ty {
        Ty::Bool => Sort::Bool,
        Ty::Float { width: 64 } => Sort::Float { eb: 11, sb: 53 },
        Ty::Float { width: 32 } => Sort::Float { eb: 8, sb: 24 },
        _ => Sort::Int,
    }
}

fn contract_sort_environment_for_body(
    body: &VerifiableBody,
) -> std::collections::BTreeMap<String, Sort> {
    let mut sorts = std::collections::BTreeMap::new();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        let Some(name) = local.name.as_ref() else { continue };
        sorts.insert(name.clone(), source_contract_sort_for_ty(&local.ty));
        if let Ty::Ref { inner, .. } = &local.ty {
            sorts.insert(format!("{name}*"), source_contract_sort_for_ty(inner));
        }
    }
    sorts.insert("_0".to_string(), source_contract_sort_for_ty(&body.return_ty));
    sorts
}

fn retype_contract_formulas_for_body(
    preconditions: &mut Vec<Formula>,
    postconditions: &mut Vec<Formula>,
    body: &VerifiableBody,
) {
    if preconditions.is_empty() && postconditions.is_empty() {
        return;
    }
    let sorts = contract_sort_environment_for_body(body);
    for formula in preconditions.iter_mut().chain(postconditions.iter_mut()) {
        let taken = std::mem::replace(formula, Formula::Bool(false));
        *formula = trust_types::retype_formula_variables(taken, &sorts);
    }
    // A contract clause is a predicate. Keep malformed non-Boolean postconditions
    // out of the reusable fact set; malformed requires are rejected by the body
    // witness gate and remain represented by their raw Contract row for tooling.
    postconditions.retain(|formula| trust_types::infer_sort(formula) == Sort::Bool);
}

/// Extract parsed contract formulas `(preconditions, postconditions)` for an
/// arbitrary `DefId`, including a **bodyless trait-method declaration**.
///
/// The native `trust_contracts` query yields nothing for a trait-method decl
/// (there is no body to attach proof facts to), but its `#[requires]` /
/// `#[ensures]` attributes are still present on the HIR node. This reads them
/// directly (via the same `hir_attrs` path as [`extract_function`]) and parses
/// them with [`trust_types::parse_spec_expr`], so a `dyn Trait` method's
/// contract can be modeled for closed-world dispatch reasoning.
///
/// Native facts only — compiler bundle / HIR attributes, no source scraping
/// (the compat lane is deleted). Returns empty vecs when the def has no recognizable
/// contract attributes. CROSS-CRATE: the native `trust_contracts` query is
/// `separate_provide_extern`, so a NON-LOCAL def's `#[requires]`/`#[ensures]`
/// are read from crate metadata too — this is required for caller-side
/// cross-crate precondition discharge to be fail-closed.
#[must_use]
pub fn extract_contract_formulas_for_def(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> (Vec<Formula>, Vec<Formula>) {
    let args = rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id);
    extract_contract_formulas_for_instance(tcx, def_id, args)
}

/// Extract contract formulas using the exact generic arguments at a call site.
///
/// A generic definition is not a typed contract identity: `f::<bool>` and
/// `f::<i32>` can give the same parameter name different solver sorts.  Callers
/// must use this entry point and key their memo/summary by `(DefId, args)`.
#[must_use]
pub fn extract_contract_formulas_for_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> (Vec<Formula>, Vec<Formula>) {
    // The authoritative source is the native typed `trust_contracts` query,
    // which yields structurally typed ensures/requires predicates for the
    // supported query vocabulary (and explicit opaque rows outside it) for any
    // def that has a body. A trait method can only carry a contract via a
    // *default body* (the contract macro rejects bodyless fns), so this covers
    // exactly the trait methods that are eligible for closed-world dispatch
    // reasoning. The `hir_attrs` fallback inside `extract_contracts` handles
    // the attribute surface when no native bundle is present.
    // Trust (cross-crate precondition discharge): read `trust_contracts` on BOTH
    // the local and non-local branch. The query is `separate_provide_extern`
    // (queries.rs:769), so it decodes from crate metadata for a NON-LOCAL def
    // exactly as it does locally. `extract_contracts` short-circuits on a
    // non-empty `compiler_contracts` bundle (lib.rs:623) before reaching its own
    // `as_local()` gate, so a populated cross-crate bundle is honored without
    // touching local-only HIR.
    let rustc_bundle = tcx.trust_contracts(def_id);
    let bundle = match convert_trust_contract_bundle(tcx, rustc_bundle) {
        Ok(bundle) => bundle,
        Err(reason) => {
            let fallback = fail_closed_caller_formulas_for_conversion_error(rustc_bundle);
            let declared_requires = rustc_bundle
                .contracts
                .iter()
                .filter(|contract| {
                    contract.kind == rustc_trust_contract::TrustContractKind::Requires
                })
                .count();
            tcx.dcx().warn(format!(
                "Trust contracts on `{}` are unsupported: {reason}; all guarantees are withheld and {declared_requires} declared caller requirement(s) fail closed",
                safe_def_path_str_with_args(tcx, def_id, args),
            ));
            return fallback;
        }
    };
    let (contracts, _report) = extract_contracts(tcx, def_id, Some(&bundle));
    let has_requires = contracts.iter().any(|contract| contract.kind == ContractKind::Requires);
    let has_ensures = contracts.iter().any(|contract| contract.kind == ContractKind::Ensures);
    if !has_requires && !has_ensures {
        return (Vec::new(), Vec::new());
    }

    let signature = match contract_signature_environment_for_def(tcx, def_id, args) {
        Ok(signature) => signature,
        Err(reason) => {
            tcx.dcx().warn(format!(
                "Trust contracts on `{}` cannot be bound to the typed function signature: {reason}; caller-side requires fail closed",
                safe_def_path_str_with_args(tcx, def_id, args),
            ));
            // Withholding a postcondition is safe. A declared requires whose
            // identity cannot be rebound must remain an impossible caller
            // obligation rather than silently disappear.
            return (
                if has_requires { vec![Formula::Bool(false)] } else { Vec::new() },
                Vec::new(),
            );
        }
    };

    let (clause_sorts, mut cached_clauses) =
        contract_sort_environment_for_clauses(&signature, &contracts, &bundle);
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();
    for (index, contract) in contracts.iter().enumerate() {
        let (target, clause) = match contract.kind {
            ContractKind::Requires => {
                (&mut preconditions, trust_types::SourceContractClause::Requires)
            }
            ContractKind::Ensures => {
                (&mut postconditions, trust_types::SourceContractClause::Ensures)
            }
            _ => continue,
        };
        let invalid = || {
            if contract.kind == ContractKind::Requires { Some(Formula::Bool(false)) } else { None }
        };
        // `Unsupported` is an explicit compiler-owned semantic state, not a
        // source predicate spelling.  Its payload is diagnostic prose (and may
        // contain quotes/backticks from the original expression), so feeding it
        // through the source parser produces a misleading parse warning at
        // every call site.  Preserve the fail-closed contract boundary
        // directly: an unsupported `requires` remains the impossible caller
        // obligation, while an unsupported `ensures` contributes no guarantee.
        if contract.body.starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX) {
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        }
        let (body, cached_parsed) = match cached_clauses.get_mut(index) {
            Some(slot) => match slot.take() {
                Some((body, parsed)) => (body, Some(parsed)),
                None => {
                    if let Some(formula) = invalid() {
                        target.push(formula);
                    }
                    continue;
                }
            },
            None => {
                let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body)
                else {
                    if let Some(formula) = invalid() {
                        target.push(formula);
                    }
                    continue;
                };
                (body, None)
            }
        };
        if let Err(error) = trust_types::validate_source_spec_expr(&body, clause, &clause_sorts)
        {
            tcx.dcx().warn(format!(
                "Trust {:?} on `{}` is not a well-typed source predicate: {error}; {}",
                contract.kind,
                safe_def_path_str_with_args(tcx, def_id, args),
                if contract.kind == ContractKind::Requires {
                    "caller-side requires fail closed"
                } else {
                    "postcondition is withheld"
                },
            ));
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        }
        let has_typed_row = bundle
            .typed_propositions
            .iter()
            .any(|proposition| proposition.source_contract_index == index);
        let formula = if let Some(proposition) = bundle.typed_proposition(index, contract) {
            proposition.formula.clone()
        } else if has_typed_row {
            tcx.dcx().warn(format!(
                "Trust {:?} on `{}` has duplicate or stale compiler-owned typed proposition provenance; {}",
                contract.kind,
                safe_def_path_str_with_args(tcx, def_id, args),
                if contract.kind == ContractKind::Requires {
                    "caller-side requires fail closed"
                } else {
                    "postcondition is withheld"
                },
            ));
            if let Some(formula) = invalid() {
                target.push(formula);
            }
            continue;
        } else {
            let maybe_formula = match cached_parsed {
                Some(parsed) => parsed,
                None => trust_types::parse_spec_expr_result(&body).ok(),
            };
            let Some(formula) = maybe_formula else {
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            };
            formula
        };
        let typed = retype_source_contract_formula(formula, &clause_sorts);
        let typed = match canonicalize_entry_collection_lengths(typed, &signature.parameters) {
            Ok(typed) => typed,
            Err(reason) => {
                tcx.dcx().warn(format!(
                    "Trust {:?} on `{}` cannot bind a collection-length accessor: {reason}; {}",
                    contract.kind,
                    safe_def_path_str_with_args(tcx, def_id, args),
                    if contract.kind == ContractKind::Requires {
                        "caller-side requires fail closed"
                    } else {
                        "postcondition is withheld"
                    },
                ));
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            }
        };
        match trust_types::check_formula_sort(&typed) {
            Ok(Sort::Bool) => target.push(typed),
            outcome => {
                // NEVER silent: this fallback makes every call site of the
                // function carry an unprovable `Bool(false)` obligation — the
                // exact "constant-true violation with an empty counterexample"
                // shape that cost a debugging session when the sort checker
                // rejected float orderings without a trace. Same warning
                // discipline as the validate-lane failure above.
                tcx.dcx().warn(format!(
                    "Trust {:?} on `{}` is not Bool-sorted after signature retyping ({outcome:?}); {}",
                    contract.kind,
                    safe_def_path_str_with_args(tcx, def_id, args),
                    if contract.kind == ContractKind::Requires {
                        "caller-side requires fail closed"
                    } else {
                        "postcondition is withheld"
                    },
                ));
                if let Some(formula) = invalid() {
                    target.push(formula);
                }
                continue;
            }
        }
    }
    (preconditions, postconditions)
}

/// Trust (2026-09-29): does a DIRECT call to `def_id` owe its caller a declared
/// precondition — would [`extract_contract_formulas_for_instance`] hand the
/// direct-call lane a NON-EMPTY `requires` set for it?
///
/// That function returns preconditions exactly when the contract set it reads
/// carries a `Requires` clause (a clause it cannot convert, bind, type or parse
/// still becomes `Formula::Bool(false)`, never nothing), and it reads the set in
/// one of two places: the compiler's `trust_contracts` bundle when that is
/// non-empty (a bundle that fails to convert keeps every declared `Requires` as
/// `false`), else a LOCAL def's HIR contract attributes (`extract_contracts`).
/// This asks the same two places the same question, WITHOUT converting, typing
/// or parsing anything, so it emits no diagnostic and cannot disagree with the
/// direct-call lane in the unsound direction: an unparseable `requires` is a
/// `requires` here too. It over-approximates only where the direct lane would
/// reject the contract outright (a synthetic-parameter collision, which is a
/// hard error on its own).
///
/// The question matters because a function with such a precondition is
/// verified as its own root only UNDER it: its body obligations are proved with
/// the `requires` as an entry hypothesis, and each direct caller is charged a
/// `Precondition` row for it. A route that reaches the function without a direct
/// call — a reified fn pointer, the function item handed to generic code — has
/// no such row, so "verified as its own root" is not a licence to call it there.
///
/// A LOCAL def for which `TrustContractBundle::def_may_have_contracts` is false
/// skips the query: that predicate is the local provider's own first line, which
/// answers such a def with an empty bundle, so the answer is the same (the HIR
/// attributes below decide it either way). `trust_contracts` is `cache_on_disk`
/// and meant to run only for contract-bearing items, the metadata encoder
/// pre-filters the same way, and the MIR inliner's keep-call rule
/// (`requires_callee_inlining`) asks this of every inline candidate.
#[must_use]
pub fn def_owes_caller_precondition(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let bundle_may_be_non_empty = def_id.as_local().is_none_or(|local_def_id| {
        rustc_trust_contract::TrustContractBundle::def_may_have_contracts(tcx, local_def_id)
    });
    if bundle_may_be_non_empty {
        let rustc_bundle = tcx.trust_contracts(def_id);
        if !rustc_bundle.contracts.is_empty() {
            return rustc_bundle.contracts.iter().any(|contract| {
                contract.kind == rustc_trust_contract::TrustContractKind::Requires
            });
        }
    }
    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
    // Trust (CONTRACT-NS-1): the same whole-path reader `extract_contracts` uses, so a
    // definition owes its callers exactly the preconditions its body assumes.
    tcx.hir_attrs(hir_id)
        .iter()
        .any(|attr| contract_kind_from_attr(attr) == Some(ContractKind::Requires))
}

/// A failed compiler-bundle conversion must not become an empty successful
/// contract set. Every declared `requires` remains an impossible caller
/// obligation and every `ensures` is withheld. Loop clauses are reported by
/// the conversion error and make whole-function verification unsupported.
fn fail_closed_caller_formulas_for_conversion_error(
    bundle: &rustc_trust_contract::TrustContractBundle<'_>,
) -> (Vec<Formula>, Vec<Formula>) {
    let has_requires = bundle
        .contracts
        .iter()
        .any(|contract| contract.kind == rustc_trust_contract::TrustContractKind::Requires);
    (if has_requires { vec![Formula::Bool(false)] } else { Vec::new() }, Vec::new())
}

fn retype_source_contract_formula(
    formula: Formula,
    signature_sorts: &std::collections::BTreeMap<String, Sort>,
) -> Formula {
    let mut extra_sorts: Option<std::collections::BTreeMap<String, Sort>> = None;
    trust_types::for_each_free_variable_name(&formula, &mut |name| {
        if signature_sorts.contains_key(name)
            || extra_sorts.as_ref().is_some_and(|s| s.contains_key(name))
        {
            return;
        }
        if let Some(base) = name.strip_prefix("old_") {
            if let Some(sort) = signature_sorts.get(base) {
                extra_sorts
                    .get_or_insert_with(|| signature_sorts.clone())
                    .insert(name.to_string(), sort.clone());
                return;
            }
        }
        let synthetic_base = name
            .strip_suffix("__len")
            .or_else(|| name.strip_suffix("__discr"))
            .or_else(|| name.strip_suffix("__value"))
            .or_else(|| name.strip_suffix("__sign"));
        if synthetic_base.is_some_and(|base| signature_sorts.contains_key(base)) {
            extra_sorts
                .get_or_insert_with(|| signature_sorts.clone())
                .insert(name.to_string(), Sort::Int);
        }
        // A FIELD-CHAIN var (`self.0`, `self*.0.0`, `self.0[3].1`) deliberately gets
        // NO entry: the signature environment carries only bare parameter names
        // (plus `<p>*` pointees and `_0`), and a field's type is not recoverable
        // from the name alone here. Forcing `Int` (the old behavior) clobbered the
        // parser's float coercion on f64 field bounds — `self.0 <= 1.0e30` parses
        // Float-sorted, and an Int-clobbered operand either fails the Bool sort
        // check (requires fails closed) or mis-sorts the caller-side Precondition
        // VC. Missing the map keeps the PARSED sort, mirroring the body lane
        // (`contract_sort_environment_for_body`), where field-chain names likewise
        // miss the exact-name retype map. A wrongly-parsed sort can only fail to
        // match downstream — the caller obligation stays (fail-closed).
    });
    match &extra_sorts {
        Some(sorts) => trust_types::retype_formula_variables(formula, sorts),
        None => trust_types::retype_formula_variables(formula, signature_sorts),
    }
}

struct ContractSignatureEnvironment {
    sorts: std::collections::BTreeMap<String, Sort>,
    parameters: Vec<(String, Ty)>,
}

fn contract_signature_environment_for_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> Result<ContractSignatureEnvironment, String> {
    let signature = tcx.fn_sig(def_id).instantiate(tcx, args).skip_binder();
    let inputs = signature.inputs();
    let identities = tcx.fn_arg_idents(def_id);
    if identities.len() != inputs.len() {
        return Err(format!(
            "parameter identity count {} does not match signature input count {}",
            identities.len(),
            inputs.len(),
        ));
    }

    let mut sorts = std::collections::BTreeMap::new();
    let mut parameters = Vec::with_capacity(inputs.len());
    for (index, (identity, input)) in identities.iter().zip(inputs.iter()).enumerate() {
        // Positional `_N` is the same deterministic fallback used by the
        // compiler's callee_param_names and MIR local naming (local 0 is return).
        let name =
            identity.map(|ident| ident.to_string()).unwrap_or_else(|| format!("_{}", index + 1));
        if let Some(collision) = trust_types::source_contract_synthetic_name_collision(&name) {
            let namespace = match collision {
                trust_types::SourceContractSyntheticNameCollision::ReturnPlace => "return-place",
                trust_types::SourceContractSyntheticNameCollision::OldValue => "pre-state",
                trust_types::SourceContractSyntheticNameCollision::PositionalPlace => {
                    "positional MIR-place"
                }
                trust_types::SourceContractSyntheticNameCollision::PredicateSymbol => {
                    "predicate-symbol"
                }
                trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata => {
                    "generated Formula metadata"
                }
            };
            return Err(format!(
                "parameter `{name}` collides with the source-contract synthetic {namespace} namespace"
            ));
        }
        if input.has_non_region_param() {
            return Err(format!(
                "parameter `{name}` remains generic after call-site instantiation"
            ));
        }
        let lowered = ty_convert::convert_ty(tcx, *input);
        sorts.insert(name.clone(), source_contract_sort_for_ty(&lowered));
        if let Ty::Ref { inner, .. } = &lowered {
            sorts.insert(format!("{name}*"), source_contract_sort_for_ty(inner));
        }
        // Projected-chain entries (`self.0`, `m.0[0].0`, `self*.2`) are NOT
        // enumerated here: `contract_sort_environment_for_clauses` resolves the
        // chains the contracts actually spell from `parameters`.
        parameters.push((name, lowered));
    }
    if signature.output().has_non_region_param() {
        return Err("return type remains generic after call-site instantiation".to_string());
    }
    let output = ty_convert::convert_ty(tcx, signature.output());
    if !matches!(output, Ty::Unit) {
        sorts.insert("_0".to_string(), source_contract_sort_for_ty(&output));
    }
    Ok(ContractSignatureEnvironment { sorts, parameters })
}

/// Return the exact instantiated parameter types used to bind a direct
/// callee's source contracts, in declaration order.
///
/// `None` is deliberately fail-closed: a direct summary without a type vector
/// cannot render generated collection-length symbols, so its length-bearing
/// preconditions remain free and non-dischargeable at the call site.
#[must_use]
pub fn extract_contract_param_types_for_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> Option<Vec<Ty>> {
    contract_signature_environment_for_def(tcx, def_id, args)
        .ok()
        .map(|signature| signature.parameters.into_iter().map(|(_, ty)| ty).collect())
}

/// Rebind the source parser's exact collection accessor leaf (`p__len`) to the
/// one length spelling consumed by MIR bounds and modular call substitution
/// (`p__slice_len`). The rebinding is authorized only by the instantiated
/// signature type. The source leaf lives in the reserved `__` family, so a
/// real parameter can never own its spelling; the collision check below is
/// retained as a defensive invariant on caller-constructed parameter lists.
fn canonicalize_entry_collection_lengths(
    mut formula: Formula,
    parameters: &[(String, Ty)],
) -> Result<Formula, String> {
    for (name, ty) in parameters {
        if !contract_ty_has_collection_length(ty) {
            continue;
        }
        let source = format!("{name}__len");
        if !trust_types::any_free_variable_name(&formula, &mut |v| v == source) {
            continue;
        }
        if parameters.iter().any(|(other, _)| other == &source) {
            return Err(format!(
                "generated accessor leaf `{source}` collides with a parameter of the same name"
            ));
        }
        formula = formula.rename_var(&source, &format!("{name}__slice_len"));
    }
    Ok(formula)
}

fn contract_ty_has_collection_length(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } => true,
        Ty::Ref { inner, .. } => contract_ty_has_collection_length(inner),
        Ty::RawPtr { pointee, .. } => contract_ty_has_collection_length(pointee),
        _ => false,
    }
}

/// Bounded depth for [`projected_leaf_sort`] — deep enough for any real
/// geometry/config aggregate (`Mat4 -> cols -> [Vec4; 4] -> field` is depth
/// 3), shallow enough that a pathological nest terminates immediately. A bound
/// on TYPE nesting (program text), never on an array length.
const PROJECTED_LEAF_DEPTH_LIMIT: u32 = 8;

/// The sort of the Bool/float/integer LEAF that the projected-chain variable
/// `name` names, resolved from the parameter TYPES, or `None` when `name` is
/// not such a chain.
///
/// A chain is a parameter head — its name, or `name*` for the pointee of a
/// reference parameter (`(*self).2` spells `self*.2`) — followed by one or more
/// STRUCT fields (`.i`, positional index — the canonicalized-contract
/// spelling), tuple fields (`.i`) and fixed-length array elements (`[k]`,
/// decimal, `k < len`), at most [`PROJECTED_LEAF_DEPTH_LIMIT`] steps. The
/// spellings are byte-identical to (a) the var names `spec_parse` lowers the
/// canonicalized contract text to and (b) `projected_chain_name` in the
/// source-contract validator, so ONE resolver types both validation and
/// retyping. ENUMS are not walked (their field view is variant-dependent — a
/// chain name would be ambiguous); symbolic-length arrays, references below
/// the head, pointers, and every other shape end the chain unresolved
/// (fail-closed: the variable keeps its parsed sort). Assigning a WRONG sort is
/// the only hazard, and the returned sort is the leaf's own
/// `source_contract_sort_for_ty`. A `&mut` pointee resolves too: the
/// environment only assigns SORTS (never truth), and the entry-stability /
/// assumption gates own the mutability soundness question.
///
/// This walks the one chain `name` spells, so its cost is `name`'s length. It
/// replaces enumerating every leaf of every parameter up front, whose count was
/// set by the types' array LENGTHS (values): that walk was capped at 64 lanes
/// per array and 512 entries per parameter.
fn projected_leaf_sort(parameters: &[(String, Ty)], name: &str) -> Option<Sort> {
    let head_end = name.find(['.', '['])?;
    let (head, mut chain) = name.split_at(head_end);
    let mut ty = match head.strip_suffix('*') {
        Some(param) => match &parameters.iter().find(|(p, _)| p == param)?.1 {
            Ty::Ref { inner, .. } => inner.as_ref(),
            _ => return None,
        },
        None => &parameters.iter().find(|(p, _)| p == head)?.1,
    };
    let canonical_decimal = |digits: &str| {
        !digits.is_empty()
            && digits.bytes().all(|b| b.is_ascii_digit())
            && (digits == "0" || !digits.starts_with('0'))
    };
    let mut depth = PROJECTED_LEAF_DEPTH_LIMIT;
    while !chain.is_empty() {
        if depth == 0 {
            return None;
        }
        depth -= 1;
        if let Some(rest) = chain.strip_prefix('.') {
            let end = rest.find(['.', '[']).unwrap_or(rest.len());
            let (digits, tail) = rest.split_at(end);
            if !canonical_decimal(digits) {
                return None;
            }
            let index: usize = digits.parse().ok()?;
            ty = match ty {
                Ty::Adt { fields, variants, .. } if variants.is_empty() => &fields.get(index)?.1,
                Ty::Tuple(items) => items.get(index)?,
                _ => return None,
            };
            chain = tail;
        } else {
            let rest = chain.strip_prefix('[')?;
            let end = rest.find(']')?;
            let digits = &rest[..end];
            if !canonical_decimal(digits) {
                return None;
            }
            let lane: u64 = digits.parse().ok()?;
            let Ty::Array { elem, len } = ty else {
                return None;
            };
            if lane >= *len {
                return None;
            }
            ty = elem;
            chain = &rest[end + 1..];
        }
    }
    matches!(ty, Ty::Bool | Ty::Float { .. } | Ty::Int { .. })
        .then(|| source_contract_sort_for_ty(ty))
}

#[inline]
fn parameter_can_have_projected_leaf(ty: &Ty) -> bool {
    let base = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    match base {
        Ty::Adt { variants, .. } => variants.is_empty(),
        Ty::Tuple(_) | Ty::Array { .. } => true,
        _ => false,
    }
}

/// The signature environment extended with the sort of every projected-chain
/// variable the contract clauses spell (see [`projected_leaf_sort`]): the
/// chains the source-contract validator looks up and the free variables of each
/// clause's formula (parsed, and the compiler-owned typed proposition when one
/// exists). Cost is linear in the clauses' text.
fn contract_sort_environment_for_clauses<'a>(
    signature: &'a ContractSignatureEnvironment,
    contracts: &[Contract],
    bundle: &trust_types::CompilerContractBundle,
) -> (
    std::borrow::Cow<'a, std::collections::BTreeMap<String, Sort>>,
    Vec<Option<(String, Option<Formula>)>>,
) {
    if !signature.parameters.iter().any(|(_, ty)| parameter_can_have_projected_leaf(ty)) {
        return (std::borrow::Cow::Borrowed(&signature.sorts), Vec::new());
    }
    let mut sorts = std::borrow::Cow::Borrowed(&signature.sorts);
    let mut cached_clauses = vec![None; contracts.len()];
    let mut add = |name: &str| {
        if sorts.contains_key(name) {
            return;
        }
        if let Some(sort) = projected_leaf_sort(&signature.parameters, name) {
            sorts.to_mut().insert(name.to_string(), sort);
        }
    };
    for (index, contract) in contracts.iter().enumerate() {
        let clause = match contract.kind {
            ContractKind::Requires => trust_types::SourceContractClause::Requires,
            ContractKind::Ensures => trust_types::SourceContractClause::Ensures,
            _ => continue,
        };
        if !contract.body.starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX) {
            if let Some(body) = normalized_contract_spec_body(contract.kind, &contract.body) {
                for name in trust_types::source_spec_projected_chain_names(&body, clause) {
                    add(&name);
                }
                let parsed = trust_types::parse_spec_expr_result(&body).ok();
                if let Some(formula) = &parsed {
                    trust_types::for_each_free_variable_name(formula, &mut |name| {
                        add(name);
                    });
                }
                cached_clauses[index] = Some((body, parsed));
            }
        }
        if let Some(proposition) = bundle.typed_proposition(index, contract) {
            trust_types::for_each_free_variable_name(&proposition.formula, &mut |name| {
                add(name);
            });
        }
    }
    (sorts, cached_clauses)
}

fn extract_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    purpose: ExtractionPurpose,
    debug_names: &FxHashMap<usize, String>,
) -> VerifiableBody {
    // verifier-coverage: the body's own typing env is the sound
    // context for revealing `impl Trait` (opaque) alias types in local /
    // return positions. On the optimized (Runtime-phase) MIR the verifier
    // runs on, this is `TypingEnv::post_analysis(..)`, the mode in which
    // rustc resolves an alias's concrete underlying type within its defining
    // scope. `convert_ty_in_env` resolves monomorphic opaque/projection/inherent
    // aliases and fails safe to `Unsupported` otherwise — see
    // `ty_convert::normalize_alias`.
    let typing_env = body.typing_env(tcx);

    let use_shared_body_memo = ty_convert::body_ty_memo_active(tcx);
    let mut local_ty_memo = ty_convert::BodyLocalTyMemo::default();
    let mut locals: Vec<LocalDecl> = Vec::with_capacity(body.local_decls.len());
    for (local, decl) in body.local_decls.iter_enumerated() {
        let index = local.as_usize();
        let ty = if use_shared_body_memo {
            ty_convert::convert_ty_in_env(tcx, typing_env, decl.ty)
        } else {
            local_ty_memo.convert_local_ty(tcx, typing_env, decl.ty)
        };
        locals.push(LocalDecl { index, ty, name: debug_names.get(&index).cloned() });
    }

    let return_ty = locals.first().map(|decl| decl.ty.clone()).unwrap_or_else(|| {
        if use_shared_body_memo {
            ty_convert::convert_ty_in_env(tcx, typing_env, body.local_decls[mir::RETURN_PLACE].ty)
        } else {
            local_ty_memo.convert_local_ty(tcx, typing_env, body.local_decls[mir::RETURN_PLACE].ty)
        }
    });

    // Trust (F6 monomorphization gap): a by-reference
    // `<num_rational::Ratio<num_bigint::BigInt> as …>::method(&self)` call is fully
    // monomorphized (the callee's `generic_args` carry the concrete `BigInt`), yet
    // the receiver LOCAL's lowered type can carry the identity-substituted
    // `Ratio<T>` (element = un-substituted `TyKind::Param`) — which
    // `authenticate_arbitrary_precision` correctly refuses (fail-closed), leaving
    // the F6 bridge gate stampless and every by-ref num-rational read/predicate
    // UNKNOWN. Recover the stamp the CONCRETE call already proves by
    // re-authenticating each direct, non-generic call's concrete receiver with the
    // SOLE `StableCrateId`-gated writer and rewriting the receiver local's stamp.
    // See `convert::refine_bignum_receiver_stamps` (soundness argument there).
    convert::refine_bignum_receiver_stamps(tcx, body, &mut locals);

    // Trust (OVF-ASSERT-XCRATE-1, 2026-10-06): an optional overflow assert is erased
    // only where THIS session codegens the body; a foreign body's assert keeps its
    // panic edge (`convert::OptionalOverflowAssertCodegen`). A codegen extraction
    // emits the body in this session.
    let overflow_assert_session = convert::OptionalOverflowAssertBodySession::of(
        tcx,
        body,
        purpose == ExtractionPurpose::Codegen,
    );
    let mut span_cache: FxHashMap<rustc_span::Span, SourceSpan> = FxHashMap::default();
    let mut blocks = Vec::with_capacity(body.basic_blocks.len());
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        blocks.push(convert::convert_basic_block_cached(
            tcx,
            bb,
            bb_data,
            Some(body),
            Some(typing_env),
            // Trust (GCKA-SELF-CALL-2, 2026-10-10): `body` is its item's own
            // MIR or a concrete instantiation of it (every instantiating
            // extraction refuses a residual parameter), so its item is the
            // caller `func_operand_name` reads a direct self call against.
            Some(body.source.def_id()),
            overflow_assert_session.for_terminator(body, bb_data.terminator()),
            &mut span_cache,
        ));
    }

    let mut vbody = VerifiableBody {
        locals,
        blocks,
        arg_count: body.arg_count,
        return_ty,
        datatype_defs: Default::default(),
    };
    if purpose == ExtractionPurpose::Verification && !ty_convert::faithful_scalars() {
        // These rewrites are proof-oriented normalizations. Even where they are
        // logically equivalent, they are not a one-to-one executable lowering,
        // so codegen-purpose and faithful paths retain the original MIR shape.
        // Trust (EXTRACT-REWRITE-1): no `Range::contains` rewrite. It keyed std's range
        // on the rendered callee path, never matched std's turbofish-suffixed
        // `contains::<U>`, and did match a user type named `RangeInclusive`; see the
        // tombstone in `convert.rs`.
        convert::rewrite_str_len_calls(tcx, body, &mut vbody);
        convert::discharge_provably_safe_pointer_asserts(tcx, body, &mut vbody);
        // Sound per-call-site total-sentinel rewrite of transparent-thiserror
        // `<dyn Error>::source` (proof-only normalization; gated on TRUST_ERRSOURCE_DEVIRT).
        convert::stamp_errsource_devirt_total_calls(tcx, body, &mut vbody);
        // Spawn calls deliberately retain their authenticated def-path unchanged.
        // A callee-name suffix is not proof authority, so extraction never stamps one.
    }
    // Trust: stamp the TyCtxt-vetted exhaustiveness flag onto SwitchInt
    // terminators so the native CHC translator can refute the otherwise-
    // `Unreachable` arm of a full enum match. Runs after lowering because it
    // needs the lowered locals/blocks AND the rustc `mir::Body`.
    mark_exhaustive_enum_unreachable_switches(tcx, body, &mut vbody);
    // OPAQUE-SCALAR-ID-1 / OPAQUE-REF-ID-1: give every runtime-value / unkeyed-constant
    // `OpaqueScalar`, every opaque reference carrier (`OpaqueConst`, `UnitVariantRef`,
    // `StructScalarFieldsRef`) and every `Operand::Unsupported` the symbol of its own
    // MIR site. Last, so no rewrite above can
    // move a statement after its site was recorded (a later pass that does is
    // re-placed by trust-vcgen's generation entry).
    vbody.place_opaque_values();
    // Preserve every Drop terminator. In particular, value provenance alone never
    // rewrites a `std::io::Error` Drop into a branch; downstream classification must
    // use authenticated type evidence and otherwise fail closed.
    vbody
}

/// Recover direct parameter bindings from HIR when optimized MIR no longer
/// retains a `VarDebugInfo` row for them.
///
/// The recovery is deliberately narrow: only plain by-value bindings from a
/// body whose parameter count exactly matches MIR are eligible. Existing MIR
/// debug names remain authoritative, and any source-name collision fails
/// closed for that binding instead of guessing which local it denotes.
#[cfg(test)]
fn recover_direct_parameter_names(
    tcx: TyCtxt<'_>,
    body: &mir::Body<'_>,
    local_names: &mut FxHashMap<usize, String>,
    name_locals: &mut FxHashMap<String, Vec<usize>>,
) {
    let Some(source_names) = hir_parameter_source_names(tcx, body) else {
        return;
    };
    merge_recovered_parameter_names(local_names, name_locals, body.arg_count, &source_names);
}

/// The HIR parameter spellings of `body`, in DECLARATION ORDER, one entry per
/// HIR parameter: `Some(name)` iff that parameter's pattern is a plain by-value
/// binding of a simple identifier, `None` for every other pattern.
///
/// This is a POSITIVE, LOCALLY CHECKABLE parameter-hood fact, and it is the only
/// thing that entitles a consumer to say "MIR argument `_p`'s own source name is
/// `s`". Nothing downstream may substitute an argument for it. Two consumers read
/// it and they must never disagree:
///
///   * `recover_direct_parameter_names`, which repopulates debug names when
///     optimized MIR dropped the parameter's row entirely; and
///   * `contract_assumption_gate::gate_contract_preconditions`, whose forced
///     restatement rewrites an authored `#[requires]` clause onto a parameter and
///     therefore mints an assumed fact about the CALLER's argument.
///
/// `None` for a position is load-bearing, not a formatting detail. `ref q`, `_`
/// and `q @ sub` all land here, and each one breaks the inference a row census
/// would otherwise make: `rustc_mir_build`'s `args_and_body` emits an argument's
/// debug row only under `pat.simple_ident()`, so for those patterns MIR local
/// `_p` carries NO row of the parameter's own — while `CopyProp`'s `Replacer`
/// happily rewrites BODY bindings' rows onto `_p`. A consumer that inferred
/// "the earliest row on `_p` is the parameter's" from row multiplicity alone
/// would then identify an ordinary `let` as the parameter and could restate a
/// clause about a same-spelled module `const` onto the caller's argument — a
/// false PROVE. Returning `None` here is what makes that unrepresentable.
///
/// Returns `None` (not a partly-filled vector) when the body is not local or has
/// no HIR body, so an absent HIR is never mistaken for "no named parameters".
fn hir_parameter_source_names(
    tcx: TyCtxt<'_>,
    body: &mir::Body<'_>,
) -> Option<Vec<Option<String>>> {
    let local_def_id = body.source.def_id().as_local()?;
    let hir_body = tcx.hir_maybe_body_owned_by(local_def_id)?;
    Some(
        hir_body
            .params
            .iter()
            .map(|param| match param.pat.kind {
                rustc_hir::PatKind::Binding(
                    rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                    _,
                    ident,
                    None,
                ) => Some(ident.name.to_string()),
                _ => None,
            })
            .collect::<Vec<_>>(),
    )
}

/// Merge one exact HIR parameter vector into both verifier name maps.
///
/// Recovery is all-or-nothing with respect to HIR shape: the HIR body must have
/// exactly one plain, direct binding for every MIR argument. Individual names
/// then remain fail-closed when they occupy Trust's generated namespace, repeat
/// in the HIR vector, or collide with any debug-owned local or spelling. The
/// occupancy snapshot is taken before insertion so acceptance cannot depend on
/// hash-map or parameter traversal order.
#[allow(rustc::potential_query_instability)]
fn merge_recovered_parameter_names(
    local_names: &mut FxHashMap<usize, String>,
    name_locals: &mut FxHashMap<String, Vec<usize>>,
    arg_count: usize,
    source_names: &[Option<String>],
) {
    if arg_count == 0 || source_names.len() != arg_count || source_names.iter().any(Option::is_none)
    {
        return;
    }

    let mut source_name_counts = FxHashMap::default();
    for name in source_names.iter().flatten() {
        *source_name_counts.entry(name.as_str()).or_insert(0usize) += 1;
    }
    let occupied_locals: FxHashSet<usize> = if local_names.is_empty() && name_locals.is_empty() {
        FxHashSet::default()
    } else {
        local_names.keys().copied().chain(name_locals.values().flatten().copied()).collect()
    };

    let mut accepted: Vec<(usize, &str)> = Vec::new();
    for (position, name) in source_names.iter().flatten().enumerate() {
        // A legal Rust parameter may occupy a name Trust later mints for a
        // Formula leaf (`s__slice_len`, `__trust_constparam_*`, `_0__value`,
        // etc.).  Never recover that spelling into the verifier model: the
        // per-local `_<index>` fallback is injective, while retaining the
        // source spelling could alias generated metadata even on a function
        // with no contract bundle.  Same shared predicate as
        // `build_debug_name_map` and the assumption gate's alias scan: this is
        // the second (and last) way a name could reach `LocalDecl::name`, so it
        // must refuse the reserved family too for the gate's exemption to hold.
        //
        // DEMOTION USES THE FULL CLASSIFIER, deliberately — NOT the alias scan's
        // `reserved_synthetic_debug_name`, which is the strictly narrower `__`
        // family. Demotion may be broad (a demoted name simply is not a body
        // spelling); the alias-scan EXEMPTION may not, because exempting a name
        // a user can legally bind would hide a real shadow. Sharing one predicate
        // across both silently narrowed this filter and broke 70 extractor tests.
        if trust_types::source_contract_synthetic_name_collision(name).is_some() {
            continue;
        }
        let local = position + 1;
        let name_str = name.as_str();
        if source_name_counts.get(name_str) != Some(&1)
            || occupied_locals.contains(&local)
            || name_locals.contains_key(name_str)
            || local_names.values().any(|existing| existing == name_str)
        {
            continue;
        }
        accepted.push((local, name_str));
    }

    for (local, name) in accepted {
        local_names.insert(local, name.to_string());
        name_locals.insert(name.to_string(), vec![local]);
    }
}

fn validate_codegen_fidelity<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    function: &mut VerifiableFunction,
    ty_policy: CodegenTyPolicy,
) -> Result<(), CodegenExtractionError> {
    let def_path = function.def_path.clone();
    let fail = |location: String, detail: String| CodegenExtractionError::UnsupportedMir {
        def_path: def_path.clone(),
        location,
        detail,
    };

    if function.body.locals.len() != mir_body.local_decls.len() {
        return Err(CodegenExtractionError::StructuralMismatch {
            def_path,
            detail: format!(
                "local count changed from {} to {}",
                mir_body.local_decls.len(),
                function.body.locals.len()
            ),
        });
    }
    if function.body.blocks.len() != mir_body.basic_blocks.len() {
        return Err(CodegenExtractionError::StructuralMismatch {
            def_path,
            detail: format!(
                "block count changed from {} to {}",
                mir_body.basic_blocks.len(),
                function.body.blocks.len()
            ),
        });
    }

    if let Some(detail) = codegen_ty_issue_with_policy(&function.body.return_ty, "return type", ty_policy)
    {
        return Err(fail("return type".to_string(), detail));
    }
    for (expected, local) in function.body.locals.iter().enumerate() {
        if local.index != expected {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "local declaration order changed at slot {expected}: extracted _{}",
                    local.index
                ),
            });
        }
        if let Some(detail) =
            codegen_ty_issue_with_policy(&local.ty, &format!("local _{}", local.index), ty_policy)
        {
            return Err(fail(format!("local _{}", local.index), detail));
        }
    }

    for (bb, mir_block) in mir_body.basic_blocks.iter_enumerated() {
        let block_index = bb.as_usize();
        let ir_block = &function.body.blocks[block_index];
        if ir_block.id != BlockId(block_index) {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "bb{block_index} became bb{} in extracted block order",
                    ir_block.id.0
                ),
            });
        }
        if ir_block.stmts.len() != mir_block.statements.len() {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path,
                detail: format!(
                    "bb{block_index} statement count changed from {} to {}",
                    mir_block.statements.len(),
                    ir_block.stmts.len()
                ),
            });
        }
        for (statement_index, (mir_statement, statement)) in
            mir_block.statements.iter().zip(&ir_block.stmts).enumerate()
        {
            let location = format!("bb{block_index}[{statement_index}]");
            if !codegen_statement_shape_matches(&mir_statement.kind, statement) {
                return Err(CodegenExtractionError::StructuralMismatch {
                    def_path,
                    detail: format!(
                        "{location} changed statement kind `{}` into `{}`",
                        mir_statement.kind.name(),
                        codegen_statement_name(statement)
                    ),
                });
            }
            if let Some(detail) =
                codegen_statement_issue_with_policy(statement, &function.body.locals, ty_policy)
            {
                return Err(fail(location, detail));
            }
        }

        validate_codegen_terminator(
            tcx,
            mir_body.source.def_id(),
            &def_path,
            block_index,
            mir_block.terminator(),
            &ir_block.terminator,
            function.body.blocks.len(),
        )?;
    }

    Ok(())
}

/// [`codegen_ty_issue`] with the ADT policy applied at EVERY nesting level:
/// under `AdmitFaithfulAdts`, an ADT carrying its faithful layout facts is
/// admitted (and its FIELD types are not descended into — the downstream
/// bridge/converter own their own fail-closed mapping of the def); everything
/// else defers to the strict judgment.
fn codegen_ty_issue_with_policy(ty: &Ty, context: &str, policy: CodegenTyPolicy) -> Option<String> {
    if policy == CodegenTyPolicy::AdmitFaithfulAdts {
        match ty {
            Ty::Adt { faithful_enum_repr: Some(_), .. } => return None,
            Ty::Adt { layout: Some(_), variants, .. } if variants.is_empty() => return None,
            // The FAITHFUL scalar spellings the guard mints (isize/usize/char
            // identity, `&str`): the bridge maps them onto trust-ir
            // Usize/Isize/Char/FatPtr(Str) and the converter's scalar and
            // str-formal lanes consume them. The strict lane never sees these
            // spellings (no guard), so its vocabulary is untouched.
            Ty::PtrSizedInt { .. } | Ty::Char | Ty::Str => return None,
            Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. } => {
                return codegen_ty_issue_with_policy(inner, &format!("{context} pointee"), policy);
            }
            Ty::Tuple(fields) => {
                return fields.iter().enumerate().find_map(|(index, field)| {
                    codegen_ty_issue_with_policy(
                        field,
                        &format!("{context}.{index}"),
                        policy,
                    )
                });
            }
            _ => {}
        }
    }
    codegen_ty_issue(ty, context)
}

fn codegen_ty_issue(ty: &Ty, context: &str) -> Option<String> {
    let nested = |child: &Ty, suffix: &str| codegen_ty_issue(child, &format!("{context}{suffix}"));
    match ty {
        Ty::Ref { inner, .. } => nested(inner, " pointee"),
        Ty::RawPtr { pointee, .. } => nested(pointee, " pointee"),
        Ty::Slice { elem } | Ty::Array { elem, .. } => nested(elem, " element"),
        Ty::SymArray { .. } => {
            Some(format!("{context} has a symbolic array length after monomorphization"))
        }
        Ty::Tuple(fields) => {
            fields.iter().enumerate().find_map(|(index, field)| nested(field, &format!(".{index}")))
        }
        // These verification models omit rustc's concrete field offsets,
        // discriminant encoding, vtable, or state-machine layout.
        Ty::Adt { name, faithful_enum_repr, layout, variants, .. } => Some(format!(
            "{context} uses layout-erased ADT `{name}` (faithful_enum_repr {}, layout {}, {} \
             variant(s))",
            if faithful_enum_repr.is_some() { "Some" } else { "None" },
            if layout.is_some() { "Some" } else { "None" },
            variants.len(),
        )),
        Ty::Datatype { name, .. } => Some(format!("{context} uses proof-only datatype `{name}`")),
        Ty::Closure { name, .. } => Some(format!("{context} uses layout-erased closure `{name}`")),
        Ty::Dynamic { trait_name, .. } => Some(format!(
            "{context} uses trait object `{trait_name}` without exact vtable metadata"
        )),
        Ty::Coroutine { name, .. } => {
            Some(format!("{context} uses layout-erased coroutine `{name}`"))
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            for (index, param) in sig.params.iter().enumerate() {
                if let Some(detail) = nested(param, &format!(" parameter {index}")) {
                    return Some(detail);
                }
            }
            nested(&sig.ret, " return")
        }
        Ty::Unsupported { kind, detail } => {
            Some(format!("{context} contains unsupported type `{kind}`: {detail}"))
        }
        Ty::Int { width, .. } if *width > 64 => Some(format!(
            "{context} uses a {width}-bit integer, but executable TrustIr currently preserves at most 64 bits"
        )),
        Ty::Bv(width) if *width > 64 => Some(format!(
            "{context} uses a {width}-bit bitvector, but executable TrustIr currently preserves at most 64 bits"
        )),
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => None,
        other => Some(format!(
            "{context} uses a type without codegen-fidelity classification: {other:?}"
        )),
    }
}

fn codegen_projection_issue(projection: &Projection) -> Option<String> {
    match projection {
        Projection::Field(_) | Projection::Index(_) | Projection::Deref => None,
        Projection::ConstantIndex { .. } | Projection::Subslice { .. } => None,
        Projection::Downcast(variant) => {
            Some(format!("downcast to variant {variant} lacks concrete rustc layout metadata"))
        }
        Projection::OpaqueCast(_) => {
            Some("opaque-cast projection is a verifier-only type placeholder".to_string())
        }
        Projection::UnwrapUnsafeBinder(_) => {
            Some("unsafe-binder projection is not executable TrustIr".to_string())
        }
        other => Some(format!("unclassified projection {other:?}")),
    }
}

fn codegen_place_issue(place: &Place) -> Option<String> {
    place.projections.iter().enumerate().find_map(|(index, projection)| {
        codegen_projection_issue(projection).map(|detail| format!("projection {index}: {detail}"))
    })
}

fn codegen_const_issue(value: &ConstValue) -> Option<String> {
    if value.contains_memory_image() {
        return Some(
            "ConstValue::MemoryImage requires executable allocation/provenance semantics"
                .to_string(),
        );
    }
    match value {
        ConstValue::Bool(_) | ConstValue::Unit => None,
        ConstValue::Int(_) => Some(
            "signed integer constant erases its source bit width; executable codegen cannot infer it faithfully"
                .to_string(),
        ),
        ConstValue::Uint(_, width) if *width > 64 => Some(format!(
            "{width}-bit unsigned constant exceeds executable TrustIr's 64-bit immediate width"
        )),
        ConstValue::Uint(value, width)
            if *width == 0 || *value >= (1_u128 << *width) =>
        {
            Some(format!(
                "unsigned constant {value} does not fit its declared {width}-bit width"
            ))
        }
        ConstValue::Uint(_, _) => None,
        ConstValue::FloatBits { width, .. } => Some(format!(
            "exact {width}-bit float constant has no executable TrustIr bridge lowering"
        )),
        ConstValue::Float(_) => {
            Some("legacy float constant loses its source bit width".to_string())
        }
        ConstValue::Str { .. } => Some(
            "string/byte constant is represented as a symbolic value without allocation provenance"
                .to_string(),
        ),
        ConstValue::OpaqueConst(_) => Some("opaque constant placeholder".to_string()),
        ConstValue::OpaqueScalar { .. } => Some("opaque scalar placeholder".to_string()),
        ConstValue::ConstParam { .. } => {
            Some("uninstantiated const parameter after monomorphization".to_string())
        }
        ConstValue::UnitVariantRef { .. } => Some(
            "unit-variant reference omits the referenced allocation and layout".to_string(),
        ),
        // Trust (EMPTY-CLOSURE-REF-VALUE-1): same opaque-reference carrier class.
        ConstValue::EmptyClosureRef { .. } => Some(
            "promoted empty-closure reference omits the referenced allocation".to_string(),
        ),
        // Trust: EFHT-P — same opaque-reference carrier class as the arm above.
        ConstValue::StructScalarFieldsRef { .. } => Some(
            "struct-scalar-fields reference omits the referenced allocation and layout"
                .to_string(),
        ),
        ConstValue::CallableItem { .. } => {
            Some("callable-item constant is an identity-only placeholder".to_string())
        }
        other => Some(format!("unclassified constant {other:?}")),
    }
}

fn codegen_operand_issue(operand: &Operand) -> Option<String> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => codegen_place_issue(place),
        Operand::Constant(value) => codegen_const_issue(value),
        Operand::Symbolic(_) => Some("symbolic verifier operand".to_string()),
        Operand::Unsupported { kind, detail, .. } => {
            Some(format!("unsupported operand `{kind}`: {detail}"))
        }
        other => Some(format!("unclassified operand {other:?}")),
    }
}

fn codegen_rvalue_issue(rvalue: &Rvalue) -> Option<String> {
    let operands = |values: &[&Operand]| values.iter().find_map(|op| codegen_operand_issue(op));
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => operands(&[op]),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operands(&[lhs, rhs])
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => codegen_place_issue(place),
        Rvalue::Repeat(op, _) => codegen_operand_issue(op),
        Rvalue::Aggregate(kind, values) => {
            let kind_issue = match kind {
                AggregateKind::Tuple | AggregateKind::Array | AggregateKind::RawPtr { .. } => None,
                AggregateKind::Adt { name, .. } => {
                    Some(format!("ADT aggregate `{name}` omits concrete rustc layout"))
                }
                AggregateKind::Closure { name, .. } => {
                    Some(format!("closure aggregate `{name}` omits concrete environment layout"))
                }
                AggregateKind::Coroutine { name } | AggregateKind::CoroutineClosure { name } => {
                    Some(format!("coroutine aggregate `{name}` omits concrete state layout"))
                }
                other => Some(format!("unclassified aggregate {other:?}")),
            };
            kind_issue.or_else(|| values.iter().find_map(codegen_operand_issue))
        }
        Rvalue::Unsupported { kind, detail, .. } => {
            Some(format!("unsupported rvalue `{kind}`: {detail}"))
        }
        other => Some(format!("unclassified rvalue {other:?}")),
    }
}

fn codegen_statement_shape_matches(
    mir_kind: &mir::StatementKind<'_>,
    statement: &Statement,
) -> bool {
    match (mir_kind, statement) {
        (mir::StatementKind::Assign(_), Statement::Assign { .. })
        | (mir::StatementKind::SetDiscriminant { .. }, Statement::SetDiscriminant { .. })
        | (mir::StatementKind::StorageLive(_), Statement::StorageLive(_))
        | (mir::StatementKind::StorageDead(_), Statement::StorageDead(_))
        | (mir::StatementKind::PlaceMention(_), Statement::PlaceMention(_))
        | (mir::StatementKind::Coverage(_), Statement::Coverage)
        | (mir::StatementKind::ConstEvalCounter, Statement::ConstEvalCounter)
        | (mir::StatementKind::Nop, Statement::Nop)
        | (mir::StatementKind::FakeRead(_), Statement::Nop)
        | (mir::StatementKind::AscribeUserType(_, _), Statement::Nop)
        | (mir::StatementKind::BackwardIncompatibleDropHint { .. }, Statement::Nop) => true,
        (mir::StatementKind::Intrinsic(_), Statement::Intrinsic { .. })
        | (mir::StatementKind::Intrinsic(_), Statement::Unsupported { .. }) => true,
        _ => false,
    }
}

fn codegen_statement_name(statement: &Statement) -> &'static str {
    match statement {
        Statement::Assign { .. } => "Assign",
        Statement::StorageLive(_) => "StorageLive",
        Statement::StorageDead(_) => "StorageDead",
        Statement::SetDiscriminant { .. } => "SetDiscriminant",
        Statement::Deinit { .. } => "Deinit",
        Statement::Retag { .. } => "Retag",
        Statement::PlaceMention(_) => "PlaceMention",
        Statement::Intrinsic { .. } => "Intrinsic",
        Statement::Unsupported { .. } => "Unsupported",
        Statement::Coverage => "Coverage",
        Statement::ConstEvalCounter => "ConstEvalCounter",
        Statement::Nop => "Nop",
        _ => "<unclassified>",
    }
}

/// [`codegen_statement_issue`] with the ADT policy applied to AGGREGATE
/// builds: under `AdmitFaithfulAdts`, an `Rvalue::Aggregate` of an ADT kind is
/// judged by the DESTINATION LOCAL's extracted type — if that type is
/// faithful-admitted (an enum with `faithful_enum_repr`, a struct with a
/// recorded layout), the build is expressible downstream (the trust-ir bridge
/// lowers exactly these constructs for the differential's oracle on every
/// local body) and only the OPERANDS are checked. `SetDiscriminant` follows
/// the same rule through its place. Everything else defers to the strict
/// judgment, and the strict lane never takes this path.
fn codegen_statement_issue_with_policy(
    statement: &Statement,
    locals: &[LocalDecl],
    policy: CodegenTyPolicy,
) -> Option<String> {
    if policy == CodegenTyPolicy::AdmitFaithfulAdts {
        let faithful_place = |place: &Place| {
            locals.get(place.local).is_some_and(|decl| {
                codegen_ty_issue_with_policy(&decl.ty, "aggregate destination", policy).is_none()
            })
        };
        match statement {
            Statement::Assign { place, rvalue: Rvalue::Aggregate(kind, values), .. }
                if matches!(kind, AggregateKind::Adt { .. }) && faithful_place(place) =>
            {
                return values.iter().find_map(codegen_operand_issue);
            }
            Statement::SetDiscriminant { place, .. } if faithful_place(place) => {
                return None;
            }
            // UNCHECKED arithmetic (`unchecked_add` in core's checked_add
            // fast path): machine-wise the plain wrapping op — the trust-ir
            // bridge lowers it under the R87 discipline (integer destination
            // required, UB modeled as the wrapping concretization the machine
            // executes). Judge operands and destination like a BinaryOp.
            Statement::Assign { place, rvalue: Rvalue::UncheckedBinaryOp(_, lhs, rhs), .. } => {
                return codegen_place_issue(place)
                    .or_else(|| codegen_operand_issue(lhs))
                    .or_else(|| codegen_operand_issue(rhs));
            }
            _ => {}
        }
    }
    codegen_statement_issue(statement)
}

fn codegen_statement_issue(statement: &Statement) -> Option<String> {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            codegen_place_issue(place).or_else(|| codegen_rvalue_issue(rvalue))
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => codegen_place_issue(place),
        Statement::PlaceMention(place) => codegen_place_issue(place),
        Statement::Intrinsic { name, .. } => {
            Some(format!("intrinsic `{name}` has no codegen-faithful memory/effect lowering"))
        }
        Statement::Unsupported { kind, detail, .. } => {
            Some(format!("unsupported statement `{kind}`: {detail}"))
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => None,
        other => Some(format!("unclassified statement {other:?}")),
    }
}

fn validate_codegen_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    // Trust (GCKA-SELF-CALL-2, 2026-10-10): the item whose MIR `mir_terminator` is
    // in, so the call is named exactly as its extraction named it.
    caller: DefId,
    def_path: &str,
    block: usize,
    mir_terminator: &mir::Terminator<'tcx>,
    terminator: &Terminator,
    block_count: usize,
) -> Result<(), CodegenExtractionError> {
    let unsupported = |detail: String| CodegenExtractionError::UnsupportedMir {
        def_path: def_path.to_string(),
        location: format!("bb{block} terminator"),
        detail,
    };
    let abstraction = |detail: String| CodegenExtractionError::SemanticAbstraction {
        def_path: def_path.to_string(),
        block,
        detail,
    };

    if let mir::TerminatorKind::Call { func, target: None, .. } = &mir_terminator.kind {
        let callee = convert::func_operand_name(tcx, Some(caller), func);
        if convert::is_total_noreturn_call(&callee) {
            return Err(abstraction(format!(
                "MIR Call `{callee}` has process-termination semantics, but executable TrustIr has no process-exit terminator (the verifier model uses Return)"
            )));
        }
    }

    if let Terminator::Opaque { kind, targets, .. } = terminator {
        return Err(unsupported(format!("opaque terminator `{kind}` with targets {targets:?}")));
    }

    // Trust (never-typed divergence, 2026-09-18): a call with NO normal-return
    // target — a panic terminal, a bulk-allocation sink, or (since
    // `convert::direct_callee_returns_never`) any callee rustc types `-> !`,
    // `process::exit` included — has no EXECUTABLE TrustIr representation: there
    // is no no-return call instruction and no process-exit terminator, so a
    // codegen consumer would have to invent a continuation the program does not
    // have. Refuse it HERE, on the shape, rather than leaving it to the unwind
    // check below, which only catches the `Cleanup`/`Continue` spellings and
    // would ACCEPT the nounwind one. This is the property the disabled
    // `is_total_noreturn_call` guard above states for `process::exit`, asserted
    // for every diverging call instead of for one forgeable display path; it is
    // the fail-closed direction in every case (an `Err` where the lane might
    // otherwise have proceeded), and the VERIFIER lane is untouched by it.
    if let Terminator::Call { func: callee, target: None, .. } = terminator {
        return Err(abstraction(format!(
            "MIR Call `{callee}` diverges (no normal-return target), but executable TrustIr \
             has no no-return call terminator"
        )));
    }

    match (&mir_terminator.kind, terminator) {
        (mir::TerminatorKind::Goto { target, .. }, Terminator::Goto(ir_target))
            if ir_target.0 == target.as_usize() => {}
        (
            mir::TerminatorKind::SwitchInt { discr, targets },
            Terminator::SwitchInt { discr: ir_discr, targets: ir_targets, otherwise, .. },
        ) => {
            let exact_targets = targets
                .iter()
                .map(|(value, target)| (value, BlockId(target.as_usize())))
                .eq(ir_targets.iter().copied());
            if !exact_targets || otherwise.0 != targets.otherwise().as_usize() {
                return Err(abstraction("SwitchInt targets changed during extraction".to_string()));
            }
            if let Some(detail) = codegen_operand_issue(ir_discr) {
                return Err(unsupported(format!("SwitchInt discriminant: {detail}")));
            }
            let _ = discr;
        }
        (mir::TerminatorKind::Return, Terminator::Return)
        | (mir::TerminatorKind::Unreachable, Terminator::Unreachable) => {}
        (
            mir::TerminatorKind::Call { func, args, destination: _, target, unwind, .. },
            Terminator::Call {
                func: callee,
                args: ir_args,
                dest,
                target: ir_target,
                is_foreign,
                ..
            },
        ) => {
            if !matches!(unwind, mir::UnwindAction::Unreachable) {
                return Err(unsupported(format!(
                    "call unwind action `{unwind:?}` is not represented by TrustIr"
                )));
            }
            if !matches!(func, mir::Operand::Constant(constant)
                if matches!(constant.const_.ty().kind(), rustc_middle::ty::TyKind::FnDef(..)))
            {
                return Err(unsupported(
                    "indirect call target has no executable callable representation".to_string(),
                ));
            }
            if callee == convert::TRUST_TOTAL_CLONE_SENTINEL
                || callee.contains("::<__trust_try_total>")
                || callee.contains(trust_types::TRUST_ELEM_BYTES_TOKEN_PREFIX)
                || callee.contains("::<__trust_str_index>")
            {
                return Err(unsupported(format!("verifier-only callable placeholder `{callee}`")));
            }
            if *is_foreign {
                return Err(unsupported(format!(
                    "foreign call `{callee}` lacks exact ABI metadata"
                )));
            }
            if args.len() != ir_args.len()
                || target.map(|target| BlockId(target.as_usize())) != *ir_target
            {
                return Err(abstraction(format!(
                    "call `{callee}` arguments or normal target changed"
                )));
            }
            if let Some(detail) = codegen_place_issue(dest) {
                return Err(unsupported(format!("call destination: {detail}")));
            }
            if let Some(detail) = ir_args.iter().find_map(codegen_operand_issue) {
                return Err(unsupported(format!("call argument: {detail}")));
            }
        }
        (
            mir::TerminatorKind::TailCall { func, args, .. },
            Terminator::TailCall { func: callee, args: ir_args, is_foreign, .. },
        ) => {
            if !matches!(func, mir::Operand::Constant(constant)
                if matches!(constant.const_.ty().kind(), rustc_middle::ty::TyKind::FnDef(..)))
            {
                return Err(unsupported(
                    "indirect tail-call target has no executable callable representation"
                        .to_string(),
                ));
            }
            if *is_foreign {
                return Err(unsupported(format!(
                    "foreign tail call `{callee}` lacks exact ABI metadata"
                )));
            }
            if args.len() != ir_args.len() {
                return Err(abstraction(format!(
                    "tail call `{callee}` arguments changed during extraction"
                )));
            }
            if let Some(detail) = ir_args.iter().find_map(codegen_operand_issue) {
                return Err(unsupported(format!("tail-call argument: {detail}")));
            }
        }
        (mir::TerminatorKind::Call { func, .. }, Terminator::Return) => {
            return Err(abstraction(format!(
                "MIR Call `{func:?}` was rewritten into an ordinary Return (noreturn/exit semantics lost)"
            )));
        }
        (mir::TerminatorKind::Call { .. }, other) => {
            return Err(abstraction(format!(
                "MIR Call was rewritten into {}",
                codegen_terminator_name(other)
            )));
        }
        (mir::TerminatorKind::Assert { .. }, _) => {
            return Err(unsupported(
                "Assert omits the exact panic payload and executable unwind edge".to_string(),
            ));
        }
        (mir::TerminatorKind::Drop { .. }, _) => {
            return Err(unsupported(
                "Drop omits the concrete drop-glue instance and executable unwind edge".to_string(),
            ));
        }
        (mir::TerminatorKind::FalseEdge { real_target, .. }, Terminator::Goto(target))
        | (mir::TerminatorKind::FalseUnwind { real_target, .. }, Terminator::Goto(target))
            if target.0 == real_target.as_usize() => {}
        (mir::TerminatorKind::CoroutineDrop, Terminator::Return) => {}
        (mir::TerminatorKind::UnwindResume, _) => {
            return Err(unsupported(
                "UnwindResume has no executable exception-handling lowering".to_string(),
            ));
        }
        (mir::TerminatorKind::UnwindTerminate(reason), _) => {
            return Err(unsupported(format!(
                "UnwindTerminate::{reason:?} has no distinct executable sink"
            )));
        }
        (original, extracted) => {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path: def_path.to_string(),
                detail: format!(
                    "bb{block} terminator `{}` became `{}`",
                    original.name(),
                    codegen_terminator_name(extracted)
                ),
            });
        }
    }

    for successor in terminator.unguarded_successors() {
        if successor.0 >= block_count {
            return Err(CodegenExtractionError::StructuralMismatch {
                def_path: def_path.to_string(),
                detail: format!(
                    "bb{block} has out-of-range successor bb{} for {block_count} blocks",
                    successor.0
                ),
            });
        }
    }
    Ok(())
}

fn codegen_terminator_name(terminator: &Terminator) -> &'static str {
    match terminator {
        Terminator::Goto(_) => "Goto",
        Terminator::SwitchInt { .. } => "SwitchInt",
        Terminator::Return => "Return",
        Terminator::Call { .. } => "Call",
        Terminator::TailCall { .. } => "TailCall",
        Terminator::Assert { .. } => "Assert",
        Terminator::Drop { .. } => "Drop",
        Terminator::Opaque { .. } => "Opaque",
        Terminator::Unreachable => "Unreachable",
        Terminator::Resume => "Resume",
        _ => "<unclassified>",
    }
}

/// Set `exhaustive_enum_unreachable` on every lowered `SwitchInt` whose selector
/// is a genuine single-assignment enum-discriminant temp, whose explicit case
/// values are EXACTLY the enum's full valid discriminant tag set, and whose
/// `otherwise` arm is `Unreachable`. Only such switches may have
/// `selector ∈ {case values}` conjoined into the default arm downstream, so
/// plain-integer switches and partial matches keep their genuine
/// `unreachable_unchecked` UB (Unknown/Fail). Reuses the exact tag-set / gating
/// machinery of `enum_discriminant_range_preconditions`.
fn mark_exhaustive_enum_unreachable_switches<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    use std::collections::BTreeSet;

    let mut has_unreachable = false;
    let mut has_switch_int = false;
    for b in &vbody.blocks {
        match b.terminator {
            Terminator::Unreachable => has_unreachable = true,
            Terminator::SwitchInt { .. } => has_switch_int = true,
            _ => {}
        }
        if has_unreachable && has_switch_int {
            break;
        }
    }
    if !has_unreachable || !has_switch_int {
        return;
    }

    // (1) discriminant-temp tag sets — identical to
    // `enum_discriminant_range_preconditions`: `_d = Discriminant(src)` with a
    // whole-local dest maps `d` to the enum's full tag set.
    let mut discr_tags: FxHashMap<usize, Vec<i128>> = FxHashMap::default();
    // Trust: piece #13 step-2 — locals `_d = Discriminant(coroutine_src)`. A
    // coroutine's resume-STATE discriminant switch has an `otherwise ->
    // Unreachable` arm that is genuinely infeasible; recognized STRUCTURALLY (no
    // layout query — that would cycle, E0391) below.
    let mut coroutine_discr_temps: FxHashSet<usize> = FxHashSet::default();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let mir::StatementKind::Assign((place, mir::Rvalue::Discriminant(src))) =
                &stmt.kind
            else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            if let Some(tags) = place_enum_tags(tcx, body, src) {
                discr_tags.insert(place.local.as_usize(), tags);
            } else if place_ty_is_coroutine(tcx, body, src) {
                coroutine_discr_temps.insert(place.local.as_usize());
            }
        }
    }
    if discr_tags.is_empty() && coroutine_discr_temps.is_empty() {
        return;
    }

    // (2) single-assignment write counts — identical to the gate in
    // `enum_discriminant_range_preconditions` (built from immutable views first
    // so they don't alias the `&mut vbody.blocks` borrow below).
    let write_counts = local_write_counts(vbody);

    let arg_count = vbody.arg_count;
    // Otherwise-target reachability snapshot: which lowered blocks end in
    // `Unreachable`, keyed by the block's own `BlockId` (not its vec position,
    // so the `otherwise` BlockId lookup is correct even if blocks are reordered).
    let unreachable_blocks: FxHashSet<usize> = vbody
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Unreachable))
        .map(|b| b.id.0)
        .collect();
    let locals = &vbody.locals;
    let local_ty = |idx: usize| -> Option<&Ty> {
        locals
            .get(idx)
            .filter(|l| l.index == idx)
            .or_else(|| locals.iter().find(|l| l.index == idx))
            .map(|l| &l.ty)
    };

    for block in &mut vbody.blocks {
        let Terminator::SwitchInt {
            discr, targets, otherwise, exhaustive_enum_unreachable, ..
        } = &mut block.terminator
        else {
            continue;
        };
        // (a) selector is a whole-local enum-discriminant temp, single-assigned,
        // non-argument, integer-sorted.
        let Some(d) = whole_local_operand(discr) else { continue };
        // Trust: piece #13 step-2 — a COROUTINE resume-STATE discriminant switch.
        // Its `otherwise -> Unreachable` arm is genuinely infeasible (the state is
        // always one of the declared coroutine states), so mark it exhaustive.
        // Recognized structurally (source is a coroutine + single-assigned u32 temp
        // + unreachable otherwise); NO tag-set equality check — computing the tag
        // set needs the coroutine LAYOUT query, which cycles inside this MIR pass
        // (E0391). rustc emits the `otherwise -> unreachable` ONLY when the switch
        // cases cover all valid states, so it is itself the exhaustiveness
        // certification. The same single-assignment / non-arg / integer-sort gates
        // apply so a mutated or non-state selector is excluded.
        if coroutine_discr_temps.contains(&d) {
            if d <= arg_count
                || write_counts.get(d).copied() != Some(1)
                || !matches!(local_ty(d), Some(Ty::Int { .. }))
            {
                continue;
            }
            if unreachable_blocks.contains(&otherwise.0) {
                *exhaustive_enum_unreachable = true;
            }
            continue;
        }
        let Some(tags) = discr_tags.get(&d) else { continue };
        let Some(discr_ty @ Ty::Int { .. }) = local_ty(d) else { continue };
        if tags.is_empty()
            || d <= arg_count
            || write_counts.get(d).copied() != Some(1)
        {
            continue;
        }
        // (b) explicit case values == FULL valid tag set (equality, not subset).
        //
        // BOTH SIDES ARE DECODED. `tags` are decoded at the extraction boundary
        // (`place_enum_tags`); the MIR arm labels are raw two's-complement bit
        // patterns and are decoded HERE, under the discriminant temp's own
        // declared width/signedness. This pair used to be raw-vs-raw, which
        // agreed by accident; decoding only one side would silently stop this
        // gate from ever firing on a negative-tag enum. A label the temp's type
        // cannot represent aborts the whole comparison (fail closed — the
        // switch is simply not marked exhaustive).
        let Some(cases) = targets
            .iter()
            .map(|(v, _)| discr_ty.decode_switch_label(*v))
            .collect::<Option<BTreeSet<i128>>>()
        else {
            continue;
        };
        let full: BTreeSet<i128> = tags.iter().copied().collect();
        if cases != full {
            continue;
        }
        // (c) otherwise target's terminator is `Unreachable`.
        if !unreachable_blocks.contains(&otherwise.0) {
            continue;
        }
        *exhaustive_enum_unreachable = true;
    }
}

/// A switch discriminant operand resolved to a whole-local index, or `None` for
/// projected / constant / symbolic operands (which can never be a plain
/// single-assignment discriminant temp).
fn whole_local_operand(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Build the RAW debug-info name → locals multimap (no last-write-wins
/// collapse). The assumption gate needs multiplicity: optimized MIR copy-prop
/// can attach a shadowed binding's debug entry to another local — including a
/// different parameter's — which the collapsed map hides.
pub fn build_debug_name_multimap(body: &mir::Body<'_>) -> FxHashMap<String, Vec<usize>> {
    use rustc_middle::mir::VarDebugInfoContents;
    if body.var_debug_info.is_empty() {
        return FxHashMap::default();
    }
    let mut names: FxHashMap<String, Vec<usize>> =
        FxHashMap::with_capacity_and_hasher(body.var_debug_info.len(), Default::default());

    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            if place.projection.is_empty() {
                let local = place.local.as_usize();
                let name_str = debug_info.name.as_str();
                if let Some(locals) = names.get_mut(name_str) {
                    locals.push(local);
                } else {
                    names.insert(name_str.to_string(), vec![local]);
                }
            }
        }
    }

    names
}

/// Build a map from Local index to user-visible variable name using debug info.
///
/// This map is the formula namespace: a contract clause's identifier binds the
/// local whose name here equals its spelling (`place_to_var_name` renders that
/// local under this name). It keeps ONE name per local, the last row's.
///
/// Trust #soundness (VS-1, 2026-10-04): A SPELLING WITH ROWS ON TWO LOCALS NAMES
/// NEITHER. CopyProp moves a copied binding's `var_debug_info` row onto the local
/// it was copied from, so one local can carry several rows, and the one-name
/// collapse used to run over all of them. That could HIDE that a spelling also
/// named a second local. Measured on a stage 1 at `-Cdebuginfo=2` (the level
/// cargo's dev profile uses) for
///
/// ```text
/// fn pick(x: u32, k: u32) -> u32 ensures result == x { let y = x; let x = k; x }
/// ```
///
/// the rows `x => _1, k => _2, y => _1, x => _2` collapsed to `{_1: y, _2: x}`.
/// The clause's `x` bound `_2`, which is `k`, and the FALSE clause was proved and
/// kernel-certified. A caller binds a callee's clause by parameter POSITION
/// (`mir_param_names` in `trust_verify.rs`), so `caller(a, b) { a - pick(a, b) }`
/// assumed `r == a`, its overflow row was proved and its overflow assert was
/// deleted: the verify-on binary returned `4 - 5` as `4294967295`. `flip`
/// (`let y = x; let x = y ^ 1; x`) put the shadow's row on the return place, and
/// the clause became `_0 == _0`. At `-Cdebuginfo=0` only the parameters' rows
/// survive and both clauses were refuted.
///
/// So a spelling with whole-local rows on two or more distinct locals is dropped
/// from every local BEFORE the collapse, which then picks only among spellings
/// that name exactly one local ([`collapse_debug_name_rows`]). Why that closes the
/// class for a signature clause: a plain parameter's own row is on its own local
/// (`args_and_body` emits it before any body binding exists, and `StripDebugInfo`
/// keeps every row on a parameter local). So if a parameter's spelling
/// names a local at all, every row with that spelling is on that local, and that
/// local is the parameter. A body binding that reuses the spelling on another
/// local makes it name nothing, and the clause fails closed: an identifier that
/// binds no local is never proved by the binding. `place_to_var_name` already
/// demotes a name that two extracted locals share; this applies the same rule
/// where the collapse could no longer hide the second local.
///
/// Only whole-local rows are counted. A projection row or a constant row never
/// names a local, so it cannot make a SIGNATURE clause's spelling bind the wrong
/// one: a parameter's own row is on its own local. That argument does not hold
/// for a BODY-scope clause. A loop clause's spelling means the binding in scope
/// at its loop, and when that binding's only row is a constant or a projection,
/// this map gives the spelling to an OUTER binding (the parameter). Dropping a
/// spelling with rows on two locals made that reachable in more shapes (`lp5` in
/// `loop_clause_binding.rs`, measured on a stage 1 with VS-1: a false invariant
/// proved and kernel-certified), so loop clauses are not bound by this map alone:
/// [`refuse_loop_clauses_bound_outside_their_scope`] checks every spelling a loop
/// clause reads against the HIR binding the query resolved at that loop. The
/// proofs this map's rule costs are in docs/DECISION_QUEUE.md (VS-1), and the
/// residuals in docs/KNOWN_HAZARDS.md (VS-1).
fn build_debug_name_map(body: &mir::Body<'_>) -> FxHashMap<usize, String> {
    use rustc_middle::mir::VarDebugInfoContents;
    if body.var_debug_info.is_empty() {
        return FxHashMap::default();
    }
    // Merge (2026-10-14): local main's review rounds 37-40 and upstream's VS-1
    // closed the same class. Both rules apply: a row reaches upstream's collapse
    // ([`collapse_debug_name_rows`], which drops a spelling on two locals and the
    // generated namespace) only when it is a whole, non-composite local AND its
    // spelling is not shared under the stricter count below (every row, projection,
    // constant and composite rows included, is a holder) AND its local is not an
    // unstable alias.
    // Trust #soundness (review round 37, 2026-10-02): a source name whose rows
    // name two or more DISTINCT locals names none of them. The collapse below is
    // last-write-wins per local, so for `fn f(b: u128, ..) ensures b <= u64::MAX
    // { let c = b; let b: u64 = ..; .. }` (rows `b => _1`, `c => _1`, `b => _3`)
    // the parameter took `c` and `b` survived on `_3` ALONE, where the vcgen
    // uniqueness check (which sees only the collapsed names) passed it: the
    // clause's `b` bound the u64 shadow and was proved and kernel-certified while
    // the u128 parameter broke it. Several names on ONE local (a copy-propagated
    // `let x = n`) stay admissible: that is one entity, and the forced parameter
    // restatement in `contract_assumption_gate` reads exactly those rows.
    //
    // EVERY row counts as a holder (review round 38): a row that is not a whole
    // plain local (a `debug x => const 7_u8` folded by SingleUseConsts, a
    // projection `debug b => (_1.0)`, a composite fragment) is an entity of its
    // own. Counting only plain rows let `let x = s; .. let x = 7u8;` keep `x` on
    // `s`'s local, and a loop `invariant x == 0` was proved about that local
    // while the `x` in scope is 7 (also an inner-block shadow taking the name
    // from a const-folded outer binding).
    let plain_local = |debug_info: &mir::VarDebugInfo<'_>| match &debug_info.value {
        VarDebugInfoContents::Place(place)
            if place.projection.is_empty() && debug_info.composite.is_none() =>
        {
            Some(place.local.as_usize())
        }
        _ => None,
    };
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum HolderState {
        OnePlain(usize),
        OneOpaque,
        Shared,
    }
    let mut name_holders: FxHashMap<rustc_span::Symbol, HolderState> =
        FxHashMap::with_capacity_and_hasher(body.var_debug_info.len(), Default::default());
    let mut rows_on_local: Vec<u32> = vec![0u32; body.local_decls.len()];
    let mut any_multi_row_local = false;
    for debug_info in &body.var_debug_info {
        let sym = debug_info.name;
        match plain_local(debug_info) {
            Some(local) => {
                name_holders
                    .entry(sym)
                    .and_modify(|state| {
                        if *state != HolderState::OnePlain(local) {
                            *state = HolderState::Shared;
                        }
                    })
                    .or_insert(HolderState::OnePlain(local));
                if local >= rows_on_local.len() {
                    rows_on_local.resize(local + 1, 0);
                }
                let next = rows_on_local[local].saturating_add(1);
                rows_on_local[local] = next;
                if next > 1 {
                    any_multi_row_local = true;
                }
            }
            None => {
                name_holders
                    .entry(sym)
                    .and_modify(|state| *state = HolderState::Shared)
                    .or_insert(HolderState::OneOpaque);
            }
        }
    }
    let shared = |sym: rustc_span::Symbol| {
        matches!(name_holders.get(&sym), Some(HolderState::Shared))
    };

    // Several names on ONE local are one entity only while that local's value
    // never changes (review round 39): DestinationPropagation (`-Zmir-opt-level=2`)
    // merges `let lim = a / 2` into a `k` that is later `k |= 128`, leaving
    // `debug k => _2; debug lim => _2`, and a loop `invariant lim >= 128` was
    // proved about `_2` while `lim` is `a / 2`. A local carrying two or more
    // rows keeps a name only when it has no mutating use (a parameter) or exactly
    // one (its definition).
    struct Mutations(Vec<u32>);
    impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for Mutations {
        fn visit_local(
            &mut self,
            local: mir::Local,
            context: rustc_middle::mir::visit::PlaceContext,
            _location: mir::Location,
        ) {
            if context.is_mutating_use() {
                let idx = local.as_usize();
                if idx >= self.0.len() {
                    self.0.resize(idx + 1, 0);
                }
                self.0[idx] = self.0[idx].saturating_add(1);
            }
        }
    }
    // Counted per ROW, not per distinct name (review round 40): DestinationPropagation
    // also merges two bindings of the SAME name (`let lim = a / 2; { let mut lim =
    // lim; lim |= 128; .. }`, rows `debug lim => _2` in two scopes), and a set of
    // names saw one entry and never ran the guard.
    let mut mutations = Mutations(if any_multi_row_local {
        vec![0u32; rows_on_local.len()]
    } else {
        Vec::new()
    });
    if any_multi_row_local {
        rustc_middle::mir::visit::Visitor::visit_body(&mut mutations, body);
    }
    let unstable_alias = |local: usize| {
        rows_on_local.get(local).is_some_and(|&count| count > 1) && {
            let allowed = if (1..=body.arg_count).contains(&local) { 0 } else { 1 };
            usize::try_from(mutations.0.get(local).copied().unwrap_or(0)).unwrap_or(usize::MAX)
                > allowed
        }
    };

    let rows: Vec<(usize, &str)> = body
        .var_debug_info
        .iter()
        .filter_map(|debug_info| {
            let local = plain_local(debug_info)?;
            let sym = debug_info.name;
            (!shared(sym) && !unstable_alias(local)).then_some((local, debug_info.name.as_str()))
        })
        .collect();
    collapse_debug_name_rows(&rows)
}

/// The collapse [`build_debug_name_map`] applies to the projection-free
/// `var_debug_info` rows, in MIR order, as `(local, name)`: each local gets the
/// LAST of its rows whose spelling has rows on no other local and is not in
/// Trust's generated namespace. A spelling that two distinct locals carry names
/// neither of them (VS-1; see [`build_debug_name_map`]).
fn collapse_debug_name_rows<S: AsRef<str>>(rows: &[(usize, S)]) -> FxHashMap<usize, String> {
    if rows.is_empty() {
        return FxHashMap::default();
    }
    let mut home: FxHashMap<&str, usize> =
        FxHashMap::with_capacity_and_hasher(rows.len(), Default::default());
    let mut on_two_locals: FxHashSet<&str> = FxHashSet::default();
    for (local, name) in rows {
        let name_str = name.as_ref();
        let first = *home.entry(name_str).or_insert(*local);
        if first != *local {
            on_two_locals.insert(name_str);
        }
    }

    let mut names: FxHashMap<usize, String> =
        FxHashMap::with_capacity_and_hasher(rows.len(), Default::default());
    for (local, name) in rows.iter().rev() {
        if names.contains_key(local) {
            continue;
        }
        let name_str = name.as_ref();
        if on_two_locals.contains(name_str) {
            continue;
        }
        // Trust #soundness (global generated-name collision): Rust
        // permits identifiers that occupy Trust's generated Formula
        // namespace.  Demote every such debug name to the unique
        // per-local fallback by omitting it from the extracted model.
        // This closes both `s__slice_len` vs the length of slice `s`
        // and `__trust_constparam_0_N` vs const generic `N`, including
        // contract-less bodies whose query is never evaluated.  It
        // also keeps every downstream fact producer on one spelling,
        // rather than relying on each producer to duplicate a denylist.
        // The predicate is shared with the assumption gate's alias scan
        // ON PURPOSE: that scan skips exactly the names demoted here,
        // and its soundness argument is precisely that a demoted name
        // can never be a local's extracted name. Demotion uses the FULL
        // classifier (see `merge_recovered_parameter_names`); the alias
        // scan's exemption is the narrower `__` family, and the
        // containment — exempt ⊆ demoted — is what makes it sound.
        if trust_types::source_contract_synthetic_name_collision(name_str).is_some() {
            continue;
        }
        names.insert(*local, name_str.to_string());
    }

    names
}

#[cfg(test)]
mod tests {
    use super::*;
    mod atomic_callsite;
    mod concurrency_effects;
    mod debug_wrapper_forwarding;
    mod faithful_atomic_xadd;
    mod faithful_call_identity;
    mod faithful_call_shape;
    mod faithful_constant_images;
    mod faithful_instance_bodies;
    mod faithful_kernel_datatypes;
    mod faithful_nested_enum_datatypes;
    mod faithful_vec_datatypes;
    mod fence_identity;
    mod forged_cmp_identity;
    mod forged_debug_identity;
    mod total_trait_call_identity;
    mod optional_overflow_assert_codegen;
    mod generic_call_key_alias;
    // Trust (REPR-U128-HIGH-TAG-1): a tag with no `i128` denotation is `Unsupported`.
    mod repr_u128_high_tag;
    // Trust (fix10/core-refusals, L1 + L3): the layout funnel reads monomorphic projections.
    mod every_reached_type_projections;
    // Trust (fix11, L2): the layout funnel evaluates leaf-closure constants.
    mod every_reached_type_constants;
    // Trust (2026-11-07): `walk_types_until` visits each shared subterm once.
    mod walk_types_shared_subterms;
    // Trust (R107-IDENTITY-1): std's validity wrappers are stamped from their definition.
    mod validity_wrapper_identity;
    mod concrete_const_typing;
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::collections::{BTreeMap, BTreeSet};
    use std::io;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};
    use rustc_middle::mir::trust_contract::{
        TrustContract, TrustContractBundle, TrustContractKind, TrustContractPayloadType,
        TrustContractPredicate, TrustContractPredicateKind, TrustContractSource,
        TrustContractSubject, TrustContractSummary, TrustContractVerifierSort, TrustLoopId,
    };
    use rustc_span::{DUMMY_SP, sym};

    const CONTRACT_FIXTURE_SOURCE: &str = r#"
#![feature(contracts)]

use core::contracts::{ensures, requires};

#[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

#[ensures(|ret: &i32| *ret >= 0)]
fn abs_broken(x: i32) -> i32 {
    x
}

fn no_contracts(x: i32) -> i32 {
    x + 1
}

// Legal Rust names in Trust's generated Formula namespace must be demoted even
// when there is no contract (and therefore no trust_contracts query gate).
#[allow(non_snake_case)]
fn generated_formula_name_params(
    s: &[u8],
    s__slice_len: usize,
    __trust_constparam_0_N: usize,
) -> usize {
    s.len() + s__slice_len + __trust_constparam_0_N
}

fn slice_last(s: &[u8]) -> u8 {
    s[s.len() - 1]
}

fn option_value(x: i32) -> Option<i32> {
    Some(x)
}

fn nested_loop_provenance(mut outer: u32, mut inner: i16) {
    while outer > 0 invariant outer <= 100 decreases outer {
        while inner > 0 invariant inner <= 100 decreases inner {
            inner -= 1;
        }
        outer -= 1;
    }
}

fn independent_loop_provenance(mut left: u32, mut right: u32) {
    while left > 0 invariant left <= 100 decreases left {
        left -= 1;
    }
    while right > 0 invariant right <= 100 decreases right {
        right -= 1;
    }
}

fn native_function_measure(n: u32) -> u32
    decreases n
{
    n
}

fn immutable_slice_projection(xs: &[u32], limit: u32) -> u32 {
    let first = xs[0];
    let mut index = 0;
    while index < limit invariant first == xs[0] {
        index += 1;
    }
    first
}

fn immutable_array_projection(xs: &[u32; 4], limit: u32) -> u32 {
    let first = xs[0];
    let mut index = 0;
    while index < limit invariant first == xs[0] {
        index += 1;
    }
    first
}

fn out_of_range_fixed_projection(xs: &[u32; 4], keep: bool) {
    while keep invariant xs[4] == xs[4] {}
}

// These are deliberate wrong-place tripwires. The native clause resolves the
// inner HIR binding, while a name-only MIR consumer could otherwise discard
// that unsupported by-value array and borrow the stable outer argument's
// collection identity.
fn shadowed_collection_index(xs: &[u32; 4], keep: bool) -> u32 {
    let first = xs[0];
    let xs = [0u32; 4];
    while keep invariant xs[0] == first {}
    xs[0]
}

fn shadowed_collection_length(xs: &[u32; 4], keep: bool) -> usize {
    let outer_length = xs.len();
    let xs = [0u32; 2];
    while keep invariant xs.len() == outer_length {}
    xs.len()
}

fn mutable_slice_store(xs: &mut [u32], index: usize, keep: bool) {
    while keep invariant xs.len() == xs.len() {
        xs[index] = 7;
    }
}

fn mutable_slice_retained_reborrow(xs: &mut [u32], index: usize, keep: bool) {
    let retained = &mut *xs;
    while keep invariant index == index {
        retained[index] = 7;
    }
}

fn mutable_slice_retained_return<'a>(
    xs: &'a mut [u32],
    index: usize,
    keep: bool,
) -> &'a mut [u32] {
    let retained = &mut *xs;
    while keep invariant index == index {
        retained[index] = 7;
    }
    retained
}

fn mutable_fixed_store(xs: &mut [u32; 4], keep: bool) {
    while keep invariant xs.len() == 4 {
        xs[0] = 7;
    }
}

#[inline(never)]
fn mutate_slice_through_call(xs: &mut [u32], index: usize) {
    xs[index] = 9;
}

fn mutable_slice_call_escape(xs: &mut [u32], index: usize, keep: bool) {
    while keep invariant xs.len() == xs.len() {
        mutate_slice_through_call(xs, index);
    }
}

fn mutable_slice_reseat(mut xs: &mut [u32], keep: bool) -> usize {
    while keep invariant xs.len() == xs.len() {
        xs = &mut [];
    }
    xs.len()
}

enum TrustRefDir {
    North,
    South,
}

fn trust_dir_by_value(d: TrustRefDir) -> u32 {
    match d {
        TrustRefDir::North => 1,
        TrustRefDir::South => 2,
    }
}

fn trust_dir_by_ref(d: &TrustRefDir) -> u32 {
    match d {
        TrustRefDir::North => 1,
        TrustRefDir::South => 2,
    }
}

// an `enum as int` cast reads the discriminant into a temp that does
// NOT drive an exhaustive-match `otherwise -> Unreachable` switch. The
// generalized discriminant-range precondition must still bound it.
fn trust_discr_as_int(d: TrustRefDir) -> u32 {
    let n = d as u32;
    n + 1
}
"#;
    const CONTRACT_FIXTURE_PATH: &str = "contracts_fixture.rs";
    const CALL_TARGET_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

// What core provides and the next solver's Copy fast path assumes
// (`Ty::is_trivially_pure_clone_copy`): without it, MIR building (erased
// regions, fast path) emits `copy x` for `&dyn LocalDebug` while borrowck
// (region variables, full solve) cannot prove it, an ICE at `x` below.
impl<'a, T: PointeeSized> Clone for &'a T {}
impl<'a, T: PointeeSized> Copy for &'a T {}

pub trait LocalDebug {}

#[inline(never)]
pub fn helper() -> i32 {
    7
}

pub fn caller() -> i32 {
    helper()
}

pub fn helper_fn_ptr() -> fn() -> i32 {
    helper
}

pub fn dyn_debug_ref(x: &dyn LocalDebug) -> &dyn LocalDebug {
    x
}

pub fn exit_wrapper() -> i32 {
    helper()
}

#[inline(never)]
pub fn identity<T>(value: T) -> T {
    value
}

pub fn mixed_generic_calls(flag: bool, number: i32) -> i32 {
    let _ = identity::<bool>(flag);
    identity::<i32>(number)
}

pub fn collision() -> i32 {
    1
}

pub mod trust_mir_extract_call_target_fixture {
    pub fn collision() -> i32 {
        2
    }
}
"#;
    const CALL_TARGET_FIXTURE_PATH: &str = "call_target_fixture.rs";
    const CODEGEN_FIDELITY_FIXTURE_SOURCE: &str = r#"
#[derive(Clone)]
pub struct Derived(pub u32);

#[inline(never)]
pub fn identity(x: u32) -> u32 {
    x
}

#[inline(never)]
pub fn clone_derived(value: &Derived) -> Derived {
    value.clone()
}

#[inline(never)]
pub fn exit_now() -> ! {
    std::process::exit(7)
}

#[inline(never)]
pub fn may_panic(x: u32) -> u32 {
    if x == 0 { panic!("zero") }
    x
}

#[inline(never)]
pub fn calls_may_panic(x: u32) -> u32 {
    may_panic(x)
}

#[inline(never)]
pub fn checked_add(x: u32) -> u32 {
    x + 1
}

#[inline(never)]
pub fn opaque_bytes() -> &'static [u8] {
    b"abc"
}

#[inline(never)]
pub fn spawn_with_literal_name() -> std::io::Result<std::thread::JoinHandle<()>> {
    std::thread::Builder::new()
        .name("trust-worker".to_string())
        .spawn(|| {})
}

#[inline(never)]
pub fn drop_os_error() {
    let error = std::io::Error::from_raw_os_error(5);
    drop(error);
}
"#;
    const CODEGEN_FIDELITY_FIXTURE_PATH: &str = "codegen_fidelity_fixture.rs";
    const OPTION_RETURN_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, const_trait_impl, lang_items, no_core)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "destruct"]
pub const trait Destruct: PointeeSized {}

pub mod std {
    pub mod option {
        pub enum Option<T> {
            None,
            Some(T),
        }
    }
}

pub fn option_value(x: i32) -> crate::std::option::Option<i32> {
    crate::std::option::Option::Some(x)
}
"#;
    const OPTION_RETURN_FIXTURE_PATH: &str = "option_return_fixture.rs";

    // Lever A step 2: a faithful miniature of the kernel's universe-`Level`
    // enum, compiled under `--crate-name clean_kernel` so its def path is
    // EXACTLY `clean_kernel::level::Level` — the def-path the datatype gate
    // (`is_level_datatype_target`) matches. `Param` carries the opaque `Name`,
    // mirroring `clean-kernel/src/level/mod.rs`.
    //
    // `#![no_core]` (like the `option_return`/`call_target` fixtures): the
    // in-process stage2 rustc ICEs (`bug!("expected associated item for operator
    // trait")` in `rustc_hir_typeck::method`) when compiling any std-USING
    // fixture, which is why the full-std fixture tests (contract, const-aggregate)
    // fail environmentally here. The real kernel stores the recursive children
    // behind `Arc<Level>` (= `LevelArc`); this fixture uses raw pointers, which
    // `peel_transparent_pointers` peels to `Level` EXACTLY as it peels
    // `Arc<Level>`, so the extracted datatype shape is identical. (The `Arc`/`Box`/
    // `Rc` wrapper-name recognition is covered by a pure unit test in
    // `ty_convert`.)
    const LEVEL_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

pub mod name {
    pub struct Name(pub u64);
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }
}

pub fn make_level() -> level::Level {
    level::Level::Zero
}
"#;
    const LEVEL_FIXTURE_PATH: &str = "level_fixture.rs";

    // Lever A step 5: a faithful miniature of the kernel's `Expr` STRUCT and the
    // `ExprKind` ENUM (the type the real `infer_type` matches on), compiled under
    // `--crate-name clean_kernel` with the SAME module nesting as the real kernel
    // (`expr/mod.rs` → `expr::Expr`, `expr/kind.rs` → `expr::kind::ExprKind`), so
    // the def paths are EXACTLY what the step-5 datatype gates match. The recursive
    // children use raw pointers (`*const Expr`), which `peel_transparent_pointers`
    // peels IDENTICALLY to the real kernel's `Arc<Expr>` children — so the extracted
    // datatype shape matches. `#![no_core]` for the same reason as the Level fixture
    // (the in-process stage2 rustc ICEs on any std-using fixture). `ExprKind` here
    // carries a REPRESENTATIVE subset of the real 25 variants — one of every
    // FIELD SHAPE the generic lowering must handle: a scalar (`BVar` u32), a `Level`
    // payload (`Sort`), `Name` payloads (`Const`/`Proj`), recursive `Expr` children
    // (`App`/`Lam`/`Let`/`Proj`), a `bool` (`Let`), an opaque `Literal`/`BinderData`
    // payload, a nullary variant (`SProp`), and a struct-style named-field variant
    // (`CubicalPath`). The lowering is generic over `adt_def.variants()`, so it
    // faithfully lowers whatever variant set the REAL `ExprKind` has.
    const EXPR_FIXTURE_SOURCE: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

pub mod name {
    pub struct Name(pub u64);
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }
}

pub mod expr {
    pub mod meta {
        pub struct ExprMeta(pub u64);
    }

    pub mod binder {
        pub struct BinderData(pub u64);
    }

    pub mod lit {
        pub enum Literal {
            Nat(u64),
            Str(u64),
        }
    }

    pub mod kind {
        use crate::level::Level;
        use crate::name::Name;
        use super::Expr;
        use super::binder::BinderData;
        use super::lit::Literal;

        pub enum ExprKind {
            BVar(u32),
            Sort(Level),
            Const(Name),
            App(*const Expr, *const Expr),
            Lam(BinderData, *const Expr, *const Expr),
            Let(*const Expr, *const Expr, *const Expr, bool),
            Lit(Literal),
            Proj(Name, u32, *const Expr),
            SProp,
            CubicalPath {
                ty: *const Expr,
                left: *const Expr,
                right: *const Expr,
            },
        }
    }

    pub struct Expr {
        pub kind: kind::ExprKind,
        pub meta: meta::ExprMeta,
    }
}

pub fn make_exprkind() -> expr::kind::ExprKind {
    expr::kind::ExprKind::SProp
}

pub fn wrap_expr(k: expr::kind::ExprKind, m: expr::meta::ExprMeta) -> expr::Expr {
    expr::Expr { kind: k, meta: m }
}

pub fn build_sort(l: level::Level) -> expr::kind::ExprKind {
    expr::kind::ExprKind::Sort(l)
}

pub fn build_sort_expr(l: level::Level, m: expr::meta::ExprMeta) -> expr::Expr {
    expr::Expr { kind: expr::kind::ExprKind::Sort(l), meta: m }
}
"#;
    const EXPR_FIXTURE_PATH: &str = "expr_fixture.rs";

    // WALL C (recursive-datatype-function induction lane) — the SMALLEST REAL
    // self-recursive datatype function: `mirror : &Level -> Level` over the
    // 2-constructor `Level` slice (`Zero | Succ`), the exact shape
    // trust-certify's `level_recursive_functional` discharges by `Level.rec`
    // induction. Compiled under `--crate-name clean_kernel` with the SAME
    // `level::Level` module path as the step-2 fixture, so the step-2 datatype
    // gate (`is_level_datatype_target`) fires and the enum lowers to
    // `Ty::Datatype` — this miniature deliberately carries ONLY the zero/succ
    // constructors (the recursion PRIMITIVE); the full 5-variant `Level`
    // (multi-IH `Max`/`IMax` arms) is the named follow-up.
    //
    // `#![no_core]` + raw-pointer recursive child, for the same environmental
    // reason as the Level/Expr fixtures (the in-process stage2 rustc ICEs on
    // std-using fixtures; `peel_transparent_pointers` peels `*const Level`
    // exactly as it peels the real kernel's `Arc<Level>`). The `Succ` result
    // payload reuses the local's address (`&m`) — semantically dangling at
    // runtime, but this fixture is only ever MIR-extracted, never executed,
    // and the datatype model erases the pointer indirection.
    const MIRROR_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

pub mod level {
    pub enum Level {
        Zero,
        Succ(*const Level),
    }
}

use level::Level;

pub fn mirror(l: &Level) -> Level {
    match l {
        Level::Zero => Level::Zero,
        Level::Succ(p) => {
            let m = mirror(unsafe { &**p });
            Level::Succ(&m)
        }
    }
}
"#;
    const MIRROR_FIXTURE_PATH: &str = "mirror_fixture.rs";

    // WALL C SCALED TO MUTUAL SCCs — the smallest REAL fuel-indexed mutual
    // cluster: a 3-function ring `fm -> gm -> hm -> fm` (one genuine call-graph
    // SCC of size 3, the size and shape of the kernel's
    // `infer_type <-> whnf <-> is_def_eq` cluster). The FUEL index reuses the
    // gated `level::Level` slice (`Zero | Succ` IS nat-shaped) and the payload
    // reuses the gated `expr::kind::ExprKind` path (2-ctor `A | B` slice), so
    // BOTH enums lower to `Ty::Datatype` through the existing step-2/step-5
    // def-path gates — no extractor changes needed for the mutual fixture.
    // Each member matches fuel first (Zero => per-constructor identity rebuild,
    // NO calls), then the payload; the `Succ` arm's `B` case calls the NEXT
    // ring member at the one-step-smaller fuel — exactly the shape
    // trust-vcgen's `mutual_recursive_datatype_functional` lane walks.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror fixture (the
    // fixture is only ever MIR-extracted, never executed).
    const MUTUAL_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

pub mod level {
    pub enum Level {
        Zero,
        Succ(*const Level),
    }
}

pub mod expr {
    pub mod kind {
        pub enum ExprKind {
            A,
            B(*const ExprKind),
        }
    }
}

use expr::kind::ExprKind;
use level::Level;

pub fn fm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = gm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}

pub fn gm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = hm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}

pub fn hm(fuel: &Level, e: &ExprKind) -> ExprKind {
    match fuel {
        Level::Zero => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => ExprKind::B(unsafe { &**x }),
        },
        Level::Succ(k) => match e {
            ExprKind::A => ExprKind::A,
            ExprKind::B(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                ExprKind::B(&m)
            }
        },
    }
}
"#;
    const MUTUAL_FIXTURE_PATH: &str = "mutual_fixture.rs";

    // THE LITERAL-CLUSTER fixture — the extraction twin of the combined
    // literal-cluster lane (multi-IH constructors, opaque payload fields,
    // model=reference postconditions; see trust-integration-tests'
    // `mutual_literal_cluster_e2e`). A genuine 2-SCC model cluster {fm, gm}
    // and a 2-SCC reference cluster {fr, gr} over the FULL 5-constructor
    // `level::Level` payload (`Zero | Succ | Max | IMax | Param(Name)` — the
    // def-path-gated full Level slice: Max/IMax carry TWO recursive fields,
    // Param an opaque `name::Name`), fuel-indexed by the def-path-gated
    // `expr::kind::ExprKind` path carrying a nat-shaped `Z | S` slice (the
    // mutual lane's fuel gate is STRUCTURAL, not name-bound, so any gated
    // 2-ctor nat shape indexes it). Model members rebuild per-constructor at
    // fuel Z; reference members return the payload DIRECTLY at fuel Z (which
    // needs `Level: Copy` — methodless lang-item impls below) — two pointwise
    // equal but STRUCTURALLY different folds. `gm_wrong` is the extracted
    // NEGATIVE-control body: identical to `gm` except its IMax step arm
    // rebuilds `Max` — wrong in ONE branch of a two-IH arm.
    //
    // `#[inline(never)]`: fm/gm and fr/gr protect themselves (rustc's MIR
    // inliner refuses SCC-internal inlining) but `gm_wrong -> fm` is NOT in
    // any cycle with `fm`, so without the attribute the inliner may flatten
    // fm's body into gm_wrong and destroy the cluster-call shape.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror/mutual
    // fixtures (the fixture is only ever MIR-extracted, never executed).
    const LITERAL_CLUSTER_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

// no_core carries NO builtin Copy impls for primitives; the lang-item traits
// here are methodless, so these empty impls are the whole story. They are
// needed so `Name` and `Level` (u64 / raw-pointer fields) can be `Copy` —
// which the REFERENCE members' direct fuel-Z return (`*e`) and the `Param`
// arms' opaque-field copy (`*n`) require.
impl Clone for u64 {}
impl Copy for u64 {}
impl<T> Clone for *const T {}
impl<T> Copy for *const T {}

pub mod name {
    pub struct Name(pub u64);

    impl crate::Clone for Name {}
    impl crate::Copy for Name {}
}

pub mod level {
    use crate::name::Name;

    pub enum Level {
        Zero,
        Succ(*const Level),
        Max(*const Level, *const Level),
        IMax(*const Level, *const Level),
        Param(Name),
    }

    impl crate::Clone for Level {}
    impl crate::Copy for Level {}
}

pub mod expr {
    pub mod kind {
        pub enum ExprKind {
            Z,
            S(*const ExprKind),
        }
    }
}

use expr::kind::ExprKind;
use level::Level;

#[inline(never)]
pub fn fm(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = gm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = gm(unsafe { &**k }, unsafe { &**a });
                let mb = gm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = gm(unsafe { &**k }, unsafe { &**a });
                let ib = gm(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gm(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fm(unsafe { &**k }, unsafe { &**a });
                let mb = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fm(unsafe { &**k }, unsafe { &**a });
                let ib = fm(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gm_wrong(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => Level::Succ(unsafe { &**x }),
            Level::Max(a, b) => Level::Max(unsafe { &**a }, unsafe { &**b }),
            Level::IMax(a, b) => Level::IMax(unsafe { &**a }, unsafe { &**b }),
            Level::Param(n) => Level::Param(*n),
        },
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fm(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fm(unsafe { &**k }, unsafe { &**a });
                let mb = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fm(unsafe { &**k }, unsafe { &**a });
                let ib = fm(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn fr(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => *e,
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = gr(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = gr(unsafe { &**k }, unsafe { &**a });
                let mb = gr(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = gr(unsafe { &**k }, unsafe { &**a });
                let ib = gr(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}

#[inline(never)]
pub fn gr(fuel: &ExprKind, e: &Level) -> Level {
    match fuel {
        ExprKind::Z => *e,
        ExprKind::S(k) => match e {
            Level::Zero => Level::Zero,
            Level::Succ(x) => {
                let m = fr(unsafe { &**k }, unsafe { &**x });
                Level::Succ(&m)
            }
            Level::Max(a, b) => {
                let ma = fr(unsafe { &**k }, unsafe { &**a });
                let mb = fr(unsafe { &**k }, unsafe { &**b });
                Level::Max(&ma, &mb)
            }
            Level::IMax(a, b) => {
                let ia = fr(unsafe { &**k }, unsafe { &**a });
                let ib = fr(unsafe { &**k }, unsafe { &**b });
                Level::IMax(&ia, &ib)
            }
            Level::Param(n) => Level::Param(*n),
        },
    }
}
"#;
    const LITERAL_CLUSTER_FIXTURE_PATH: &str = "literal_cluster_fixture.rs";

    // THE CELL-COUNTER fixture — the INTERIOR-MUTABILITY extraction-gap
    // prototype (the heartbeat `Cell<u32>` residual). A genuine 2-SCC model
    // cluster {fm, gm} whose budget lives in an interior-mutable cell on a
    // `&Tc` parameter (the literal `TypeChecker` discipline: read the counter
    // at entry, fail-closed exhaustion on `Z`, write the decremented counter
    // back, call the sibling THROUGH the same `&Tc` — the remainder is never
    // passed or returned, it lives in the cell), plus the hand-THREADED
    // reference 2-SCC {fr, gr} in exactly the `threaded_budget_functional`
    // lane shape (`(&Fuel, &E) -> Res` with `Res = Mk(Fuel, E)`).
    //
    // The interior mutability is the REAL mechanism: a `#[lang = "unsafe_cell"]`
    // struct (the same lang item `core::cell::Cell` is built on) wrapped by
    // `FuelCell` with `#[inline(never)]` accessor fns `cell_get`/`cell_set` —
    // the accessor-CALL recognition mirrors how the real `Cell::<u32>::get/set`
    // std fns would be recognized by def-path. `&self` is modeled as the
    // explicit `tc: &Tc` first parameter (identical MIR: `self` IS `_1`).
    //
    // `fm_leak` is the fail-closed NEGATIVE control: it passes `tc` to a
    // function outside the recognized accessor/cluster-call grammar (an escape
    // through which the cell could be mutated), so `thread_cell_state` must
    // refuse it.
    //
    // `#![no_core]` + raw-pointer recursive children + address-of-local result
    // payloads, for the same environmental reasons as the mirror/mutual/
    // literal-cluster fixtures (the fixture is only ever MIR-extracted, never
    // executed).
    const CELL_COUNTER_FIXTURE_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

// The REAL interior-mutability mechanism: the same lang item `core::cell`
// is built on. `FuelCell` plays `Cell<u32>` (the heartbeat counter), with the
// nat-shaped `Fuel` standing in for the numeric budget (the fuel lanes'
// standing u32-as-nat modeling step).
#[lang = "unsafe_cell"]
#[repr(transparent)]
pub struct UnsafeCell<T> {
    value: T,
}

impl<T> Clone for *const T {}
impl<T> Copy for *const T {}

pub mod fuel {
    pub enum Fuel {
        Z,
        S(*const Fuel),
    }

    impl crate::Clone for Fuel {}
    impl crate::Copy for Fuel {}
}

pub mod expr {
    pub enum E {
        A,
        B(*const E),
        M(*const E, *const E),
    }

    impl crate::Clone for E {}
    impl crate::Copy for E {}
}

pub mod res {
    use crate::expr::E;
    use crate::fuel::Fuel;

    pub enum Res {
        Mk(Fuel, E),
    }
}

use expr::E;
use fuel::Fuel;
use res::Res;

pub struct FuelCell {
    value: UnsafeCell<*const Fuel>,
}

pub struct Tc {
    pub heartbeat: FuelCell,
}

#[inline(never)]
pub fn cell_get(c: &FuelCell) -> *const Fuel {
    unsafe { *(&c.value as *const UnsafeCell<*const Fuel> as *const *const Fuel) }
}

// `allow(invalid_reference_casting)`: the write really is through the
// `#[lang = "unsafe_cell"]` wrapper (defined behavior — the same cast
// `core::cell::UnsafeCell::get` performs); the lint's heuristic just does not
// recognize the hand-rolled no_core spelling.
#[allow(invalid_reference_casting)]
#[inline(never)]
pub fn cell_set(c: &FuelCell, v: *const Fuel) {
    unsafe {
        *(&c.value as *const UnsafeCell<*const Fuel> as *mut *const Fuel) = v;
    }
}

// ── The MODEL cluster: budget in the cell, never in the signature ────────────

#[inline(never)]
pub fn fm(tc: &Tc, e: &E) -> E {
    match unsafe { &*cell_get(&tc.heartbeat) } {
        Fuel::Z => *e,
        Fuel::S(k) => {
            cell_set(&tc.heartbeat, *k);
            match e {
                E::A => E::A,
                E::B(x) => {
                    let r = gm(tc, unsafe { &**x });
                    E::B(&r)
                }
                E::M(x, y) => {
                    let r1 = gm(tc, unsafe { &**x });
                    let r2 = gm(tc, unsafe { &**y });
                    E::M(&r1, &r2)
                }
            }
        }
    }
}

#[inline(never)]
pub fn gm(tc: &Tc, e: &E) -> E {
    match unsafe { &*cell_get(&tc.heartbeat) } {
        Fuel::Z => *e,
        Fuel::S(k) => {
            cell_set(&tc.heartbeat, *k);
            match e {
                E::A => E::A,
                E::B(x) => {
                    let r = fm(tc, unsafe { &**x });
                    E::B(&r)
                }
                E::M(x, y) => {
                    let r1 = fm(tc, unsafe { &**x });
                    let r2 = fm(tc, unsafe { &**y });
                    E::M(&r1, &r2)
                }
            }
        }
    }
}

// ── The NEGATIVE control: `tc` ESCAPES the accessor/cluster-call grammar ─────

#[inline(never)]
pub fn leak(_tc: &Tc) {}

#[inline(never)]
pub fn fm_leak(tc: &Tc, e: &E) -> E {
    let _p = cell_get(&tc.heartbeat);
    leak(tc);
    *e
}

// ── The hand-THREADED reference cluster (already in the lane shape) ──────────

#[inline(never)]
pub fn fr(fuel: &Fuel, e: &E) -> Res {
    match fuel {
        // `*fuel` (the exhausted input, which IS `Z` in this arm) rather than a
        // fresh `Fuel::Z`: a constructed fieldless variant inside an aggregate
        // argument gets const-promoted to an opaque constant at
        // -Zmir-opt-level=3, which the threaded lane's symbolic walk cannot
        // resolve; the runtime copy of the matched-on param resolves under the
        // Z branch.
        Fuel::Z => Res::Mk(*fuel, *e),
        Fuel::S(k) => match e {
            E::A => Res::Mk(unsafe { **k }, E::A),
            E::B(x) => {
                let r = gr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(rf, rv) = r;
                Res::Mk(rf, E::B(&rv))
            }
            E::M(x, y) => {
                let r1 = gr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(r1f, r1v) = r1;
                let r2 = gr(&r1f, unsafe { &**y });
                let Res::Mk(r2f, r2v) = r2;
                Res::Mk(r2f, E::M(&r1v, &r2v))
            }
        },
    }
}

#[inline(never)]
pub fn gr(fuel: &Fuel, e: &E) -> Res {
    match fuel {
        Fuel::Z => Res::Mk(*fuel, *e),
        Fuel::S(k) => match e {
            E::A => Res::Mk(unsafe { **k }, E::A),
            E::B(x) => {
                let r = fr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(rf, rv) = r;
                Res::Mk(rf, E::B(&rv))
            }
            E::M(x, y) => {
                let r1 = fr(unsafe { &**k }, unsafe { &**x });
                let Res::Mk(r1f, r1v) = r1;
                let r2 = fr(&r1f, unsafe { &**y });
                let Res::Mk(r2f, r2v) = r2;
                Res::Mk(r2f, E::M(&r1v, &r2v))
            }
        },
    }
}
"#;
    const CELL_COUNTER_FIXTURE_PATH: &str = "cell_counter_fixture.rs";

    struct InMemoryContractFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryContractFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CONTRACT_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CONTRACT_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected contract fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in contract tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCallTargetFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCallTargetFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CALL_TARGET_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CALL_TARGET_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected call target fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in call-target tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCodegenFidelityFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCodegenFidelityFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CODEGEN_FIDELITY_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CODEGEN_FIDELITY_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected codegen-fidelity fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in codegen-fidelity tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryOptionReturnFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryOptionReturnFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(OPTION_RETURN_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(OPTION_RETURN_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected option return fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in option return tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryLevelFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryLevelFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(LEVEL_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(LEVEL_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected level fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in level tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryExprFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryExprFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(EXPR_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(EXPR_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected expr fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in expr tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryMirrorFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryMirrorFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(MIRROR_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(MIRROR_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected mirror fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in mirror tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryMutualFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryMutualFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(MUTUAL_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(MUTUAL_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected mutual fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in mutual tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryLiteralClusterFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryLiteralClusterFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(LITERAL_CLUSTER_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(LITERAL_CLUSTER_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected literal-cluster fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in literal-cluster tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCellCounterFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCellCounterFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CELL_COUNTER_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CELL_COUNTER_FIXTURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected cell-counter fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in cell-counter tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct LevelExtractionCallbacks {
        level_ty: Option<Ty>,
        /// Trust: the DEFINITIONS collected while lowering. Since the
        /// body-de-duplication landing (`ty_convert.rs`, "WHAT LANDED IS `Def1`
        /// WITH THE BODY DE-DUPLICATED"), a canonical cut point is a by-name
        /// marker at EVERY occurrence and its one definition is materialized
        /// into `datatype_defs`. So the lowered `Ty` alone no longer carries the
        /// variant list, and a test that reads only the `Ty` is asserting the
        /// pre-landing shape.
        level_defs: trust_types::DatatypeDefs,
        /// Diagnostic: every nominal-ADT type seen while scanning, so a miss
        /// surfaces the actual def paths instead of an opaque `None`.
        probe: Vec<String>,
    }

    /// Lever A step 5 — extracts BOTH the `Expr` struct and the `ExprKind` enum
    /// datatype from one compile of the expr fixture (mirrors `LevelExtractionCallbacks`).
    struct ExprExtractionCallbacks {
        exprkind_ty: Option<Ty>,
        expr_ty: Option<Ty>,
        /// Trust: the definitions collected alongside. A canonical cut point
        /// lowers to a by-name marker at every occurrence since the
        /// body-de-duplication landing, so the lowered `Ty` alone no longer
        /// carries its variants — same reason `extract_level_datatype_fixture`
        /// returns them.
        defs: trust_types::DatatypeDefs,
        /// Diagnostic: every nominal-ADT type seen while scanning.
        probe: Vec<String>,
    }

    impl rustc_driver::Callbacks for ExprExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryExprFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                    continue;
                }
                let body = tcx.optimized_mir(did);
                for local in &body.local_decls {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = local.ty.kind() {
                        let path = safe_def_path_str(tcx, adt_def.did());
                        self.probe.push(path.clone());
                        // Local-crate defs render WITHOUT the crate-name prefix; an
                        // upstream dependency would render with it. Accept either,
                        // and match EXACTLY (no suffix) so `expr::Expr` and
                        // `expr::kind::ExprKind` never cross-classify.
                        // Trust: M6 rung-7 sweep — `body` is a real compiled MIR body, so
                        // use its own `typing_env` (matching `extract_body`'s locals)
                        // instead of the plain env-less `convert_ty`. These extraction
                        // helpers scan the SAME `Expr`/`ExprKind` recursive-ADT family
                        // rung-7 diagnosed the closure-capture divergence on; the current
                        // `#![no_core]` fixture (no aliases) never exercises the gap, but
                        // this closes it by construction for any future fixture that does.
                        if matches!(
                            path.as_str(),
                            "expr::kind::ExprKind" | "clean_kernel::expr::kind::ExprKind"
                        ) && self.exprkind_ty.is_none()
                        {
                            self.exprkind_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                        }
                        if matches!(path.as_str(), "expr::Expr" | "clean_kernel::expr::Expr")
                            && self.expr_ty.is_none()
                        {
                            let _scope = ty_convert::DatatypeDefScope::begin();
                            self.expr_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                            self.defs.extend(ty_convert::collected_datatype_defs());
                        }
                    }
                }
            }
            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for LevelExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryLevelFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            // Look at EVERY nominal-ADT definition in the crate directly (an enum
            // inside `mod level` is not a crate-root free item, so a MIR-local scan
            // can miss it). `hir_body_owners` + `optimized_mir` locals are scanned
            // too as a fallback / to mirror the real extraction path.
            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                    continue;
                }
                let body = tcx.optimized_mir(did);
                for local in &body.local_decls {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = local.ty.kind() {
                        let path = safe_def_path_str(tcx, adt_def.did());
                        self.probe.push(path.clone());
                        // Local-crate defs render WITHOUT the crate-name prefix
                        // (`level::Level`); an upstream dependency would render
                        // `clean_kernel::level::Level`. Accept either.
                        let is_level =
                            matches!(path.as_str(), "level::Level" | "clean_kernel::level::Level");
                        // Trust: M6 rung-7 sweep — use `body`'s own `typing_env`, same as
                        // the `ExprExtractionCallbacks` fix above.
                        if is_level && self.level_ty.is_none() {
                            // Trust: collect inside a scope, then take the defs
                            // with the type -- the definition lives in the side
                            // table, not in the returned `Ty`.
                            let _scope = ty_convert::DatatypeDefScope::begin();
                            self.level_ty = Some(ty_convert::convert_ty_in_env(
                                tcx,
                                body.typing_env(tcx),
                                local.ty,
                            ));
                            self.level_defs = ty_convert::collected_datatype_defs();
                        }
                    }
                }
            }
            Compilation::Stop
        }
    }

    struct ContractExtractionCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
        metadata: BTreeMap<String, TrustMetadata>,
        empty_bundle_metadata: BTreeMap<String, TrustMetadata>,
        loop_contract_bundles: BTreeMap<String, CompilerContractBundle>,
        loop_provenance_failures: BTreeMap<String, Vec<(u32, String)>>,
        function_decreases_bundle: Option<CompilerContractBundle>,
        conversion_fixture: Option<ContractConversionFixture>,
        query_contracts: Option<CompilerContractBundle>,
    }

    impl rustc_driver::Callbacks for ContractExtractionCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryContractFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let def_id = item.owner_id.def_id.to_def_id();
                    let body = tcx.optimized_mir(def_id);
                    let name = ident.name.to_string();
                    // Mirror the production verifier path: built-in contract
                    // attributes are consumed by rustc and arrive at extraction
                    // through the typed `trust_contracts` query bundle. A bare
                    // `extract_function(..., None)` cannot and must not recover
                    // them from source text.
                    let mut compiler_contracts =
                        convert_trust_contract_bundle(tcx, tcx.trust_contracts(def_id))
                            .expect("rustc query payload should convert for fixture functions");
                    let provenance_failures =
                        stamp_loop_header_provenance(body, &mut compiler_contracts);
                    if !compiler_contracts.loop_contracts.is_empty() {
                        self.loop_contract_bundles.insert(name.clone(), compiler_contracts.clone());
                        self.loop_provenance_failures.insert(name.clone(), provenance_failures);
                    }
                    if name == "native_function_measure" && self.function_decreases_bundle.is_none()
                    {
                        self.function_decreases_bundle = Some(compiler_contracts.clone());
                    }
                    self.metadata.insert(
                        name.clone(),
                        extract_metadata_with_contract_bundle(tcx, body, Some(&compiler_contracts)),
                    );
                    self.empty_bundle_metadata.insert(
                        name.clone(),
                        extract_metadata_with_contract_bundle(
                            tcx,
                            body,
                            Some(&CompilerContractBundle::default()),
                        ),
                    );
                    self.functions.insert(
                        name.clone(),
                        extract_function_with_contract_bundle(tcx, body, Some(&compiler_contracts)),
                    );
                    if name == "no_contracts" && self.conversion_fixture.is_none() {
                        self.conversion_fixture =
                            Some(build_contract_conversion_fixture(tcx, def_id));
                    }
                    if name == "reciprocal" && self.query_contracts.is_none() {
                        self.query_contracts = Some(compiler_contracts);
                    }
                }
            }

            Compilation::Stop
        }
    }

    #[derive(Debug, Default)]
    struct CallTargetFixture {
        functions: BTreeMap<String, VerifiableFunction>,
        direct_call_symbols: BTreeMap<String, Vec<String>>,
        direct_call_func_types: BTreeMap<String, Vec<Ty>>,
        canonical_def_paths: Vec<String>,
        crate_def_path: String,
    }

    struct CallTargetCallbacks {
        fixture: CallTargetFixture,
    }

    #[derive(Debug, Default)]
    struct CodegenFidelityFixture {
        verifier: BTreeMap<String, VerifiableFunction>,
        faithful_clone_caller: Option<VerifiableFunction>,
        raw_codegen: BTreeMap<String, VerifiableFunction>,
        codegen: BTreeMap<String, Result<VerifiableFunction, CodegenExtractionError>>,
    }

    struct CodegenFidelityCallbacks {
        fixture: CodegenFidelityFixture,
    }

    struct OptionReturnCallbacks {
        function: Option<VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for CallTargetCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCallTargetFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let def_id = item.owner_id.def_id.to_def_id();
                    let body = tcx.optimized_mir(def_id);
                    self.fixture.canonical_def_paths.push(safe_def_path_str(tcx, def_id));
                    self.fixture.functions.insert(fn_name.clone(), extract_function(tcx, body));
                    self.fixture
                        .direct_call_symbols
                        .insert(fn_name.clone(), direct_call_symbol_names(tcx, body));
                    self.fixture
                        .direct_call_func_types
                        .insert(fn_name, direct_call_func_types(tcx, body));
                }
            }
            self.fixture.crate_def_path =
                safe_def_path_str(tcx, rustc_span::def_id::CRATE_DEF_ID.to_def_id());

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for CodegenFidelityCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCodegenFidelityFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for def_id in tcx.hir_body_owners() {
                let did = def_id.to_def_id();
                let path = safe_def_path_str(tcx, did);
                // Local def paths may omit the crate-name prefix (for example,
                // `identity` rather than `fixture::identity`). Classify by the
                // exact final segment while retaining the enclosing-path check
                // for the generated Clone implementation.
                let leaf = path.rsplit("::").next().unwrap_or(path.as_str());
                let key = if leaf == "identity" {
                    Some("identity")
                } else if leaf == "clone_derived" {
                    Some("clone_derived")
                } else if leaf == "exit_now" {
                    Some("exit_now")
                } else if leaf == "calls_may_panic" {
                    Some("calls_may_panic")
                } else if leaf == "checked_add" {
                    Some("checked_add")
                } else if leaf == "opaque_bytes" {
                    Some("opaque_bytes")
                } else if leaf == "spawn_with_literal_name" {
                    Some("spawn_with_literal_name")
                } else if leaf == "drop_os_error" {
                    Some("drop_os_error")
                } else if leaf == "clone" && path.contains("Derived") {
                    Some("derived_clone_impl")
                } else {
                    None
                };
                let Some(key) = key else { continue };
                let body = tcx.optimized_mir(did);
                self.fixture.verifier.insert(key.to_string(), extract_function(tcx, body));
                if key == "clone_derived" {
                    self.fixture.faithful_clone_caller = Some(extract_function_faithful(tcx, body));
                }
                self.fixture.raw_codegen.insert(
                    key.to_string(),
                    extract_function_with_purpose(tcx, body, None, ExtractionPurpose::Codegen),
                );
                self.fixture
                    .codegen
                    .insert(key.to_string(), extract_function_for_codegen(tcx, body));
            }

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for OptionReturnCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryOptionReturnFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    if ident.name.as_str() == "option_value" {
                        let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                        self.function = Some(extract_function(tcx, body));
                        break;
                    }
                }
            }

            Compilation::Stop
        }
    }

    /// Lever A step 3 (real MIR body): extract EVERY free function of the Expr
    /// fixture into a `VerifiableFunction`, so a test can inspect the actual MIR
    /// body a datatype-construction function lowers to (the input that
    /// `trust-vcgen`'s datatype-functional VC-gen consumes).
    struct ExprBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for ExprBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryExprFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// WALL C — extracts every free function of the mirror fixture (the
    /// self-recursive `mirror : &Level -> Level`) into a `VerifiableFunction`
    /// (mirrors `ExprBodyCallbacks`).
    struct MirrorBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for MirrorBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryMirrorFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// WALL C scaled to MUTUAL SCCs — extracts every free function of the
    /// mutual ring fixture (`fm -> gm -> hm -> fm`) into `VerifiableFunction`s
    /// (mirrors `MirrorBodyCallbacks`).
    struct MutualBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for MutualBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryMutualFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// EXTRACTION SERIALIZATION — extracts every free function of the
    /// literal-cluster fixture (model {fm, gm} + negative `gm_wrong` +
    /// reference {fr, gr} over the FULL 5-ctor Level) into
    /// `VerifiableFunction`s (mirrors `MutualBodyCallbacks`).
    struct LiteralClusterBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for LiteralClusterBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryLiteralClusterFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    /// INTERIOR-MUTABILITY GAP — extracts every free function of the
    /// cell-counter fixture (cell accessors + cell-mediated model {fm, gm} +
    /// negative `fm_leak` + hand-threaded reference {fr, gr}) into
    /// `VerifiableFunction`s (mirrors `LiteralClusterBodyCallbacks`).
    struct CellCounterBodyCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for CellCounterBodyCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCellCounterFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.functions.insert(ident.name.to_string(), extract_function(tcx, body));
                }
            }
            Compilation::Stop
        }
    }

    pub(super) fn compiler_sysroot() -> String {
        // Bootstrap exports RUSTC_SYSROOT for the compiler BUILD, which can be
        // stage0-sysroot even while this stage1 test binary embeds a newer
        // rustc_driver.  Treat that ambient value as a last-resort candidate,
        // and validate every override before handing it to an in-process
        // compiler.  TRUST_TEST_SYSROOT is the unambiguous fixture-only escape
        // hatch; TEST_SYSROOT retains bootstrap/Cargo compatibility.
        std::env::var("TRUST_TEST_SYSROOT")
            .ok()
            .and_then(validated_trust_sysroot)
            .or_else(|| std::env::var("TEST_SYSROOT").ok().and_then(validated_trust_sysroot))
            .or_else(|| {
                option_env!("TEST_SYSROOT").map(str::to_owned).and_then(validated_trust_sysroot)
            })
            .or_else(local_trust_sysroot)
            .or_else(|| std::env::var("RUSTC_SYSROOT").ok().and_then(validated_trust_sysroot))
            .or_else(|| std::env::var("SYSROOT").ok().and_then(validated_trust_sysroot))
            .unwrap_or_else(|| {
                panic!(
                    "trust-mir-extract direct fixtures require a local Trust sysroot; \
                     set TRUST_TEST_SYSROOT/TEST_SYSROOT to a sysroot containing \
                     bin/trustc plus host core/std, or build stage1/stage2 at \
                     build/<host>. Invalid ambient RUSTC_SYSROOT/SYSROOT values \
                     are rejected rather than mixing compiler versions."
                )
            })
    }

    fn validated_trust_sysroot(candidate: String) -> Option<String> {
        let candidate = PathBuf::from(candidate);
        is_local_trust_sysroot(&candidate)
            .then(|| candidate.canonicalize().unwrap_or(candidate).to_string_lossy().into_owned())
    }

    fn local_trust_sysroot() -> Option<String> {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repo_root = manifest_dir.parent()?.parent()?;
        let mut build_roots = vec![repo_root.join("build/host")];

        if let Ok(host) = std::env::var("CFG_COMPILER_HOST_TRIPLE") {
            build_roots.push(repo_root.join("build").join(host));
        }
        for host in [
            "aarch64-unknown-linux-gnu",
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ] {
            build_roots.push(repo_root.join("build").join(host));
        }

        let candidates = build_roots
            .into_iter()
            .flat_map(|root| ["stage2", "stage1"].map(move |stage| root.join(stage)));

        candidates
            .into_iter()
            .find_map(|candidate| validated_trust_sysroot(candidate.to_string_lossy().into_owned()))
    }

    fn is_local_trust_sysroot(candidate: &Path) -> bool {
        candidate.join("bin/trustc").is_file()
            && sysroot_has_host_std(candidate)
            && sysroot_compiler_matches_driver(candidate)
    }

    /// The in-process `rustc_driver` linked into this test binary must match the
    /// compiler that built the candidate sysroot's `std`/`core`, or metadata
    /// load fails with E0514 ("found crate `std` compiled by an incompatible
    /// version of rustc"), cascading into a broken prelude and surfacing as the
    /// generic, misleading `failed to compile contract fixture` panic. When a
    /// version-skewed sysroot survives the structural check (e.g. `stage2` is a
    /// build behind `stage1` after an interrupted rebuild), skip it so
    /// resolution falls through to a matching candidate — or to the explicit
    /// no-sysroot diagnostic — instead of handing the driver a mismatched std.
    ///
    /// LENIENT by construction: it only ever REJECTS on a proven version
    /// mismatch. If the driver's own version is unknown, or the candidate's
    /// `trustc --version` cannot be queried or does not parse, the prior
    /// structural acceptance stands — a robustness gate must never turn a valid
    /// sysroot away.
    fn sysroot_compiler_matches_driver(candidate: &Path) -> bool {
        let Some(driver_version) = rustc_interface::util::rustc_version_str() else {
            return true;
        };
        let driver_version = driver_version.trim();
        if driver_version.is_empty() {
            return true;
        }
        let Ok(output) =
            std::process::Command::new(candidate.join("bin/trustc")).arg("--version").output()
        else {
            return true;
        };
        if !output.status.success() {
            return true;
        }
        // The candidate compiler built this sysroot's std, so its `--version`
        // line embeds the exact identity `rustc_version_str()` reports (e.g.
        // `1.99.0-dev (2513b19da 2026-07-21)`). A substring match tolerates the
        // surrounding `rustc … (trustc)` framing without depending on its shape.
        String::from_utf8_lossy(&output.stdout).contains(driver_version)
    }

    fn sysroot_has_host_std(candidate: &Path) -> bool {
        let Ok(entries) = candidate.join("lib/rustlib").read_dir() else {
            return false;
        };

        entries.flatten().any(|entry| {
            let lib_dir = entry.path().join("lib");
            has_rmeta(&lib_dir, "libcore-") && has_rmeta(&lib_dir, "libstd-")
        })
    }

    fn has_rmeta(lib_dir: &Path, prefix: &str) -> bool {
        let Ok(entries) = lib_dir.read_dir() else {
            return false;
        };

        entries.flatten().any(|entry| {
            let file_name = entry.file_name();
            let file_name = file_name.to_string_lossy();
            file_name.starts_with(prefix) && file_name.ends_with(".rmeta")
        })
    }

    #[derive(Debug, Default)]
    struct ContractFixture {
        functions: BTreeMap<String, VerifiableFunction>,
        metadata: BTreeMap<String, TrustMetadata>,
        empty_bundle_metadata: BTreeMap<String, TrustMetadata>,
        loop_contract_bundles: BTreeMap<String, CompilerContractBundle>,
        loop_provenance_failures: BTreeMap<String, Vec<(u32, String)>>,
        function_decreases_bundle: Option<CompilerContractBundle>,
        conversion: ContractConversionFixture,
        query_contracts: Option<CompilerContractBundle>,
    }

    #[derive(Debug, Default)]
    struct ContractConversionFixture {
        supported: CompilerContractBundle,
        unsupported: CompilerContractBundle,
        empty: CompilerContractBundle,
        mir_local_error: Option<TrustContractBundleConversionError>,
        unsupported_kind_error: Option<TrustContractBundleConversionError>,
        nonconvertible_error: Option<TrustContractBundleConversionError>,
        loop_only: CompilerContractBundle,
        mixed_loop: CompilerContractBundle,
        typed_loop: CompilerContractBundle,
        mixed_loop_caller_fallback: (Vec<Formula>, Vec<Formula>),
        loop_only_len: usize,
        loop_only_iter_count: usize,
        loop_only_is_empty: bool,
    }

    fn build_contract_conversion_fixture<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
    ) -> ContractConversionFixture {
        let mut supported = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut supported,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
        );
        push_synthetic_contract(
            tcx,
            &mut supported,
            TrustContractKind::Ensures,
            TrustContractSubject::Function,
            TrustContractPredicateKind::BoolLiteral { value: true },
        );
        refresh_synthetic_summary(&mut supported);

        let empty = TrustContractBundle::empty(def_id);

        let mut unsupported = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut unsupported,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Unsupported {
                reason: sym::trust_test_contract_not_lowered,
            },
        );
        refresh_synthetic_summary(&mut unsupported);

        let mut mir_local = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut mir_local,
            TrustContractKind::Requires,
            TrustContractSubject::Function,
            TrustContractPredicateKind::MirLocal { local: mir::Local::from_usize(1) },
        );
        refresh_synthetic_summary(&mut mir_local);

        let mut unsupported_kind = TrustContractBundle::empty(def_id);
        push_synthetic_contract(
            tcx,
            &mut unsupported_kind,
            TrustContractKind::Invariant,
            TrustContractSubject::Function,
            TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
        );
        refresh_synthetic_summary(&mut unsupported_kind);

        let mut nonconvertible = TrustContractBundle::empty(def_id);
        nonconvertible.summary.total = 1;

        let mut loop_only = TrustContractBundle::empty(def_id);
        push_synthetic_loop_contract(
            tcx,
            &mut loop_only,
            TrustContractKind::LoopInvariant,
            TrustLoopId { index: 0, hir_local_id: 1 },
        );
        push_synthetic_loop_contract(
            tcx,
            &mut loop_only,
            TrustContractKind::Decreases,
            TrustLoopId { index: 0, hir_local_id: 1 },
        );
        refresh_synthetic_summary(&mut loop_only);
        let loop_only_len = loop_only.len();
        let loop_only_iter_count = loop_only.iter_all().count();
        let loop_only_is_empty = loop_only.is_empty();

        let mut mixed_loop = supported.clone();
        push_synthetic_loop_contract(
            tcx,
            &mut mixed_loop,
            TrustContractKind::LoopInvariant,
            TrustLoopId { index: 0, hir_local_id: 1 },
        );
        refresh_synthetic_summary(&mut mixed_loop);
        let mut typed_loop = supported.clone();
        typed_loop.loop_contracts.push(TrustContract {
            kind: TrustContractKind::LoopInvariant,
            source: TrustContractSource::Native,
            subject: TrustContractSubject::HirLoop {
                id: TrustLoopId { index: 0, hir_local_id: 1 },
                loop_span: DUMMY_SP,
                header_span: DUMMY_SP,
            },
            citation: None,
            predicate: TrustContractPredicate {
                ty: TrustContractPayloadType::Verifier(TrustContractVerifierSort::Bool),
                kind: TrustContractPredicateKind::BoolLiteral { value: true },
                source_bindings: Vec::new(),
                source_place_bindings: None,
            },
            span: DUMMY_SP,
            keyword_span: Some(DUMMY_SP),
        });
        refresh_synthetic_summary(&mut typed_loop);
        let mixed_loop_caller_fallback =
            fail_closed_caller_formulas_for_conversion_error(&mixed_loop);
        ContractConversionFixture {
            supported: convert_trust_contract_bundle(tcx, &supported)
                .expect("supported synthetic bundle should convert"),
            unsupported: convert_trust_contract_bundle(tcx, &unsupported)
                .expect("unsupported predicate should be preserved for verifier API lowering"),
            empty: convert_trust_contract_bundle(tcx, &empty)
                .expect("empty synthetic bundle should convert"),
            mir_local_error: Some(
                convert_trust_contract_bundle(tcx, &mir_local)
                    .expect_err("MIR local predicate should fail closed"),
            ),
            unsupported_kind_error: Some(
                convert_trust_contract_bundle(tcx, &unsupported_kind)
                    .expect_err("unsupported kind should fail closed"),
            ),
            nonconvertible_error: Some(
                convert_trust_contract_bundle(tcx, &nonconvertible)
                    .expect_err("non-empty summary without entries should fail closed"),
            ),
            loop_only: convert_trust_contract_bundle(tcx, &loop_only)
                .expect("loop-only bundle should retain every authored loop clause"),
            mixed_loop: convert_trust_contract_bundle(tcx, &mixed_loop)
                .expect("mixed bundle should retain function and loop lanes"),
            typed_loop: convert_trust_contract_bundle(tcx, &typed_loop)
                .expect("typed loop predicate should retain structural provenance"),
            mixed_loop_caller_fallback,
            loop_only_len,
            loop_only_iter_count,
            loop_only_is_empty,
        }
    }

    fn push_synthetic_contract<'tcx>(
        tcx: TyCtxt<'tcx>,
        bundle: &mut TrustContractBundle<'tcx>,
        kind: TrustContractKind,
        subject: TrustContractSubject,
        predicate_kind: TrustContractPredicateKind,
    ) {
        bundle.contracts.push(TrustContract {
            kind,
            source: TrustContractSource::Attribute,
            subject,
            citation: None,
            predicate: TrustContractPredicate {
                ty: TrustContractPayloadType::Rust(tcx.types.bool),
                kind: predicate_kind,
                source_bindings: Vec::new(),
                source_place_bindings: None,
            },
            span: DUMMY_SP,
            keyword_span: None,
        });
    }

    fn push_synthetic_loop_contract<'tcx>(
        _tcx: TyCtxt<'tcx>,
        bundle: &mut TrustContractBundle<'tcx>,
        kind: TrustContractKind,
        id: TrustLoopId,
    ) {
        bundle.loop_contracts.push(TrustContract {
            kind,
            source: TrustContractSource::Native,
            subject: TrustContractSubject::HirLoop {
                id,
                loop_span: DUMMY_SP,
                header_span: DUMMY_SP,
            },
            citation: None,
            predicate: TrustContractPredicate {
                ty: TrustContractPayloadType::Verifier(if kind == TrustContractKind::Decreases {
                    TrustContractVerifierSort::Int
                } else {
                    TrustContractVerifierSort::Bool
                }),
                kind: TrustContractPredicateKind::Unsupported {
                    reason: sym::trust_test_contract_not_lowered,
                },
                source_bindings: Vec::new(),
                source_place_bindings: None,
            },
            span: DUMMY_SP,
            keyword_span: Some(DUMMY_SP),
        });
    }

    fn refresh_synthetic_summary(bundle: &mut TrustContractBundle<'_>) {
        let mut summary = TrustContractSummary::default();
        summary.total = bundle.len() as u32;
        for contract in bundle.iter_all() {
            match contract.kind {
                TrustContractKind::Requires => summary.requires += 1,
                TrustContractKind::Ensures => summary.ensures += 1,
                TrustContractKind::Invariant | TrustContractKind::LoopInvariant => {
                    summary.invariants += 1;
                }
                TrustContractKind::Decreases => summary.decreases += 1,
                TrustContractKind::Asserts => summary.assertions += 1,
                TrustContractKind::Assumes
                | TrustContractKind::Refinement
                | TrustContractKind::Temporal => {}
            }
            if matches!(
                &contract.predicate.kind,
                TrustContractPredicateKind::Opaque { .. }
                    | TrustContractPredicateKind::Unsupported { .. }
            ) {
                summary.opaque += 1;
            }
        }
        bundle.summary = summary;
    }

    fn extract_contract_fixture_with_mir_opt_level(mir_opt_level: u8) -> ContractFixture {
        let mut callbacks = ContractExtractionCallbacks {
            functions: BTreeMap::new(),
            metadata: BTreeMap::new(),
            empty_bundle_metadata: BTreeMap::new(),
            loop_contract_bundles: BTreeMap::new(),
            loop_provenance_failures: BTreeMap::new(),
            function_decreases_bundle: None,
            conversion_fixture: None,
            query_contracts: None,
        };
        let mut args = vec![
            "rustc".to_string(),
            CONTRACT_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_contracts_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            format!("-Zmir-opt-level={mir_opt_level}"),
            "-Zno-codegen".to_string(),
            // All embedded compiler fixtures stop during analysis.  Select
            // rustc's built-in dummy backend explicitly so unit tests neither
            // dlopen the staged default nor poison the process-global backend
            // loader when a test sysroot is incomplete. Embedded `run_compiler`
            // already selects `EmbeddedNoOfficialEvidence`; that policy both
            // disables official Trust evidence and refuses an explicit,
            // effective `-Ztrust-verify=on` (an explicit `off` is redundant).
            "-Zcodegen-backend=dummy".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile contract fixture");

        ContractFixture {
            functions: callbacks.functions,
            metadata: callbacks.metadata,
            empty_bundle_metadata: callbacks.empty_bundle_metadata,
            loop_contract_bundles: callbacks.loop_contract_bundles,
            loop_provenance_failures: callbacks.loop_provenance_failures,
            function_decreases_bundle: callbacks.function_decreases_bundle,
            conversion: callbacks
                .conversion_fixture
                .expect("synthetic contract conversion fixture should be built"),
            query_contracts: callbacks.query_contracts,
        }
    }

    fn extract_contract_fixture() -> ContractFixture {
        extract_contract_fixture_with_mir_opt_level(3)
    }

    fn extract_call_target_fixture() -> CallTargetFixture {
        let mut callbacks = CallTargetCallbacks { fixture: CallTargetFixture::default() };
        // This is a self-contained no_core fixture; requiring a staged sysroot
        // would make it depend on unrelated std assembly.
        let args = vec![
            "rustc".to_string(),
            CALL_TARGET_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_call_target_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile call-target fixture");

        callbacks.fixture
    }

    fn extract_codegen_fidelity_fixture() -> CodegenFidelityFixture {
        let mut callbacks = CodegenFidelityCallbacks { fixture: CodegenFidelityFixture::default() };
        let mut args = vec![
            "rustc".to_string(),
            CODEGEN_FIDELITY_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_codegen_fidelity_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=0".to_string(),
            "-Cdebug-assertions=yes".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile codegen-fidelity fixture");

        callbacks.fixture
    }

    fn extract_option_return_fixture() -> VerifiableFunction {
        let mut callbacks = OptionReturnCallbacks { function: None };
        let args = vec![
            "rustc".to_string(),
            OPTION_RETURN_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_option_return_fixture".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile no_core option return fixture");

        callbacks.function.expect("option_value should be extracted")
    }

    /// Returns the lowered `Level` type AND the definitions collected with it.
    ///
    /// Trust: both, because since the body-de-duplication landing the lowered
    /// `Ty` for a canonical cut point is a by-name marker and its variant list
    /// lives in `datatype_defs`. A helper that returned only the `Ty` could only
    /// support assertions about the pre-landing shape.
    fn extract_level_datatype_fixture() -> (Ty, trust_types::DatatypeDefs) {
        let mut callbacks = LevelExtractionCallbacks {
            level_ty: None,
            level_defs: Default::default(),
            probe: Vec::new(),
        };
        // no_core fixture: no `--sysroot` (no extern crates), `-Ainternal_features`
        // to allow `#![feature(lang_items, no_core)]` — mirrors the option-return
        // fixture's invocation, which compiles in-process where std fixtures ICE.
        // Embedded `run_compiler` uses `EmbeddedNoOfficialEvidence`, so native
        // Trust verification is already disabled for this extraction-only
        // fixture. The policy refuses evidence controls and an effective
        // `-Ztrust-verify=on`; an explicit `-Ztrust-verify=off` is redundant.
        let args = vec![
            "rustc".to_string(),
            LEVEL_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Level fixture");

        let level_ty = callbacks.level_ty.unwrap_or_else(|| {
            panic!(
                "clean_kernel::level::Level should be extracted; ADT locals seen: {:?}",
                callbacks.probe
            )
        });
        (level_ty, callbacks.level_defs)
    }

    /// Resolve a lowered type to the datatype whose variants it denotes.
    ///
    /// A cut point lowers to `Ty::Datatype { name, variants: [] }` -- the
    /// definition is filed once under `name` in `defs`. This follows that one
    /// hop, and is the shape every assertion about a recursive datatype's
    /// constructors has to go through now.
    fn resolve_datatype<'a>(
        ty: &'a Ty,
        defs: &'a trust_types::DatatypeDefs,
    ) -> (&'a str, &'a Vec<(String, Vec<(String, Ty)>)>) {
        let Ty::Datatype { name, variants } = ty else {
            panic!("expected a Ty::Datatype, got {ty:?}");
        };
        if !variants.is_empty() {
            return (name, variants);
        }
        let def = defs.get(name.as_str()).unwrap_or_else(|| {
            panic!(
                "`{name}` lowered to a by-name marker but no definition was filed for it; \
                 defs present: {:?}",
                defs.keys().collect::<Vec<_>>()
            )
        });
        let Ty::Datatype { variants, .. } = def else {
            panic!("the filed definition for `{name}` is not a Ty::Datatype: {def:?}");
        };
        (name, variants)
    }

    /// Lever A step 5 — compile the expr fixture in-process and return the
    /// extracted `(ExprKind, Expr)` types. Same embedded-no-evidence invocation
    /// as the Level fixture (`--crate-name clean_kernel`, `no_core`).
    fn extract_expr_datatypes_fixture() -> (Ty, Ty, trust_types::DatatypeDefs) {
        let mut callbacks = ExprExtractionCallbacks {
            exprkind_ty: None,
            expr_ty: None,
            defs: Default::default(),
            probe: Vec::new(),
        };
        let args = vec![
            "rustc".to_string(),
            EXPR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Expr fixture");

        let probe = callbacks.probe.clone();
        let exprkind_ty = callbacks.exprkind_ty.unwrap_or_else(|| {
            panic!(
                "clean_kernel::expr::kind::ExprKind should be extracted; ADT locals seen: {probe:?}"
            )
        });
        let expr_ty = callbacks.expr_ty.unwrap_or_else(|| {
            panic!("clean_kernel::expr::Expr should be extracted; ADT locals seen: {probe:?}")
        });
        (exprkind_ty, expr_ty, callbacks.defs)
    }

    /// Lever A step 3 — compile the Expr fixture and extract every free
    /// function's real MIR body as a `VerifiableFunction`.
    fn extract_expr_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = ExprBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            EXPR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel Expr fixture");
        callbacks.functions
    }

    fn debug_rows(rows: &[(usize, &str)]) -> Vec<(usize, String)> {
        rows.iter().map(|(local, name)| (*local, (*name).to_string())).collect()
    }

    /// VS-1, the measured shape: `fn pick(x: u32, k: u32) -> u32 ensures result == x
    /// { let y = x; let x = k; x }` at `-Cdebuginfo=2`, after CopyProp. The old
    /// collapse gave `{1: y, 2: x}`, so the clause's `x` bound `k`'s local.
    #[test]
    fn debug_name_collapse_drops_a_spelling_on_two_locals_pick() {
        let rows = debug_rows(&[(1, "x"), (2, "k"), (1, "y"), (2, "x")]);
        let names = collapse_debug_name_rows(&rows);
        assert_eq!(names.get(&1).map(String::as_str), Some("y"));
        assert_eq!(names.get(&2).map(String::as_str), Some("k"));
        assert!(
            !names.values().any(|name| name == "x"),
            "`x` has rows on _1 and _2, so it must name neither: {names:?}"
        );
    }

    /// VS-1 twin: `let y = x; let x = y ^ 1; x` puts the shadow's row on the RETURN
    /// place, which made the clause `result == x` read `_0 == _0`.
    #[test]
    fn debug_name_collapse_drops_a_spelling_on_two_locals_flip() {
        let names = collapse_debug_name_rows(&debug_rows(&[(1, "x"), (1, "y"), (0, "x")]));
        assert_eq!(names.get(&1).map(String::as_str), Some("y"));
        assert_eq!(names.get(&0), None, "the return place must not inherit `x`: {names:?}");
    }

    /// The collapse is unchanged where no spelling is on two locals: the last row
    /// wins (`{ let x = n; x }` names `_1` `x`, the shape the assumption gate's
    /// forced parameter restatement reads), a repeated row on ONE local is not
    /// ambiguous, and a spelling on two locals does not stop another spelling from
    /// naming one of them.
    #[test]
    fn debug_name_collapse_keeps_last_write_among_unambiguous_spellings() {
        let names = collapse_debug_name_rows(&debug_rows(&[(1, "n"), (1, "x")]));
        assert_eq!(names.get(&1).map(String::as_str), Some("x"));

        let names = collapse_debug_name_rows(&debug_rows(&[(1, "x"), (1, "x")]));
        assert_eq!(names.get(&1).map(String::as_str), Some("x"));

        let names = collapse_debug_name_rows(&debug_rows(&[(1, "x"), (1, "y"), (3, "y")]));
        assert_eq!(names.get(&1).map(String::as_str), Some("x"));
        assert_eq!(names.get(&3), None);
    }

    /// Trust's generated namespace is still demoted, also when it is the last row.
    #[test]
    fn debug_name_collapse_still_demotes_generated_spellings() {
        let names = collapse_debug_name_rows(&debug_rows(&[(1, "n"), (1, "__ret")]));
        assert_eq!(names.get(&1).map(String::as_str), Some("n"));
        let names = collapse_debug_name_rows(&debug_rows(&[(2, "s__slice_len")]));
        assert!(names.is_empty(), "{names:?}");
    }

    /// The invariant the formula namespace relies on, over every row sequence of
    /// length <= 4 on the spellings {a, b} and the locals {0, 1, 2}: a spelling the
    /// collapse keeps has ALL of its rows on the one local it names, so no two
    /// locals share it and no row of it is on another local.
    #[test]
    fn debug_name_collapse_never_keeps_a_spelling_with_rows_elsewhere() {
        let alphabet: Vec<(usize, &str)> =
            [0usize, 1, 2].iter().flat_map(|local| [(*local, "a"), (*local, "b")]).collect();
        let mut sequences: Vec<Vec<(usize, &str)>> = vec![Vec::new()];
        let mut checked = 0usize;
        for _ in 0..4 {
            let mut longer = Vec::new();
            for sequence in &sequences {
                for row in &alphabet {
                    let mut next = sequence.clone();
                    next.push(*row);
                    longer.push(next);
                }
            }
            for sequence in &longer {
                let rows = debug_rows(sequence);
                let names = collapse_debug_name_rows(&rows);
                for (local, name) in &names {
                    assert!(
                        rows.iter().filter(|(_, n)| n == name).all(|(l, _)| l == local),
                        "{name} kept on _{local} but has a row elsewhere: {rows:?} -> {names:?}"
                    );
                    assert!(rows.contains(&(*local, name.clone())));
                }
                checked += 1;
            }
            sequences = longer;
        }
        assert_eq!(checked, 6 + 36 + 216 + 1296);
    }

    #[test]
    fn recovered_parameter_names_populate_both_low_debuginfo_maps() {
        let mut local_names = FxHashMap::default();
        let mut name_locals = FxHashMap::default();
        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[Some("x".to_string()), Some("xs".to_string())],
        );

        assert_eq!(local_names.get(&1).map(String::as_str), Some("x"));
        assert_eq!(local_names.get(&2).map(String::as_str), Some("xs"));
        assert_eq!(name_locals.get("x").map(Vec::as_slice), Some(&[1][..]));
        assert_eq!(name_locals.get("xs").map(Vec::as_slice), Some(&[2][..]));
    }

    #[test]
    fn recovered_parameter_names_require_an_exact_plain_hir_vector() {
        let mut local_names = FxHashMap::default();
        let mut name_locals = FxHashMap::default();
        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[Some("n".to_string())],
        );
        assert!(local_names.is_empty());
        assert!(name_locals.is_empty());

        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            2,
            &[None, Some("plain".to_string())],
        );
        assert!(local_names.is_empty());
        assert!(name_locals.is_empty());
    }

    #[test]
    fn recovered_parameter_names_reject_occupied_duplicate_and_synthetic_names() {
        let mut local_names = FxHashMap::default();
        local_names.insert(4, "debug_name".to_string());
        let mut name_locals = FxHashMap::default();
        name_locals.insert("raw_name".to_string(), vec![5, 6]);
        name_locals.insert("local_one_is_occupied".to_string(), vec![1]);

        merge_recovered_parameter_names(
            &mut local_names,
            &mut name_locals,
            8,
            &[
                Some("candidate_for_occupied_local".to_string()),
                Some("debug_name".to_string()),
                Some("raw_name".to_string()),
                Some("candidate_for_occupied_local_four".to_string()),
                Some("duplicate".to_string()),
                Some("duplicate".to_string()),
                Some("s__slice_len".to_string()),
                Some("xs".to_string()),
            ],
        );

        // Locals occupied through either map, names occupied through either map,
        // duplicate HIR names, and Trust's generated namespace all fail closed.
        for local in [1, 2, 3, 5, 6, 7] {
            assert_eq!(local_names.get(&local), None, "local {local} was recovered");
        }
        assert_eq!(local_names.get(&4).map(String::as_str), Some("debug_name"));
        assert_eq!(local_names.get(&8).map(String::as_str), Some("xs"));
        assert_eq!(name_locals.get("xs").map(Vec::as_slice), Some(&[8][..]));
        assert!(!name_locals.contains_key("candidate_for_occupied_local"));
        assert!(!name_locals.contains_key("candidate_for_occupied_local_four"));
        assert!(!name_locals.contains_key("duplicate"));
        assert!(!name_locals.contains_key("s__slice_len"));
    }

    /// WALL C — compile the mirror fixture and extract every free function's
    /// real MIR body as a `VerifiableFunction`. Same embedded-no-evidence
    /// invocation as the Expr fixture (`--crate-name clean_kernel`, `no_core`).
    fn extract_mirror_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = MirrorBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            MIRROR_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel mirror fixture");
        callbacks.functions
    }

    /// EXTRACTION SERIALIZATION — compile the literal-cluster fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror/mutual fixtures.
    fn extract_literal_cluster_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = LiteralClusterBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            LITERAL_CLUSTER_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel literal-cluster fixture");
        callbacks.functions
    }

    /// INTERIOR-MUTABILITY GAP — compile the cell-counter fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror/mutual/literal-cluster fixtures.
    fn extract_cell_counter_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = CellCounterBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            CELL_COUNTER_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel cell-counter fixture");
        callbacks.functions
    }

    // ── EXTRACTED-ARTIFACT SERIALIZATION (the extraction -> integration
    //    hand-off) ─────────────────────────────────────────────────────────────
    //
    // trust-integration-tests cannot run the in-process rustc, so its lane
    // e2e tests consume the extractor's output through COMMITTED serialized
    // artifacts under `crates/trust-integration-tests/fixtures/extracted/`.
    // The artifacts are REGENERATED, never hand-edited: the gate tests below
    // re-extract the fixture in-process, serialize it, and compare
    // byte-for-byte against the committed file — any drift between the live
    // extractor and the committed artifact fails the suite. Regenerate with
    //
    //   TRUST_UPDATE_EXTRACTED_FIXTURES=1 <the usual trust-mir-extract --lib
    //   incantation> extracted_
    //
    // and commit the JSON together with the extractor change. The
    // serialization is pipeline plumbing, NOT TCB: the artifacts are the
    // post-conversion `VerifiableFunction` form (everything rustc-internal is
    // already gone by then), and the kernel check downstream remains the
    // authority on every proof obligation. The sole canonicalization is the
    // compiler-version salt in a single-crate fixture's `stable_crate_id`; see
    // `canonicalize_extracted_fixture_callee_ids` below.

    /// The committed artifacts directory (inside trust-integration-tests).
    fn extracted_artifacts_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-integration-tests/fixtures/extracted")
    }

    /// Synthetic, nonzero namespace assigned only in committed extracted
    /// fixtures. Its ASCII bytes spell `TRUST_FX`; production extraction never
    /// performs this substitution.
    const EXTRACTED_FIXTURE_STABLE_CRATE_ID: u64 = 0x5452_5553_545f_4658;

    /// Canonicalize the one value that cannot be committed byte-for-byte.
    ///
    /// Rustc deliberately salts every [`rustc_span::def_id::StableCrateId`]
    /// with its full compiler version, including this repository's commit. As
    /// soon as authenticated `callee_identity` became serialized, writing the
    /// freshly extracted ID and committing it changed the compiler version and
    /// therefore changed the ID again: the snapshot could never converge. The
    /// structured `callee_key` carries the same salted crate ID and must use
    /// the same fixture namespace.
    ///
    /// These four fixtures currently contain direct identities from exactly
    /// one synthetic crate. On a clone used only for the transport snapshot,
    /// replace that crate component with a fixed fixture namespace while
    /// preserving both carriers' presence, `def_index`, `substs_digest`, and
    /// all key facts. Refuse more than one observed crate ID across either
    /// carrier instead of collapsing local and foreign identities or hiding a
    /// disagreement between the carriers. Production extraction and every
    /// proof-authority consumer retain the compiler-authenticated ID.
    fn canonicalize_extracted_fixture_callee_ids(
        functions: &BTreeMap<String, VerifiableFunction>,
    ) -> BTreeMap<String, VerifiableFunction> {
        let mut canonical = functions.clone();
        let mut raw_stable_crate_id = None;

        for function in canonical.values_mut() {
            for block in &mut function.body.blocks {
                let (callee_identity, callee_key) = match &mut block.terminator {
                    Terminator::Call { callee_identity, callee_key, .. }
                    | Terminator::TailCall { callee_identity, callee_key, .. } => {
                        (callee_identity, callee_key)
                    }
                    _ => continue,
                };
                if let Some(identity) = callee_identity {
                    canonicalize_extracted_fixture_crate_id(
                        &mut raw_stable_crate_id,
                        &mut identity.stable_crate_id,
                    );
                }
                if let Some(key) = callee_key {
                    canonicalize_extracted_fixture_crate_id(
                        &mut raw_stable_crate_id,
                        &mut key.stable_crate_id,
                    );
                }
            }
        }

        canonical
    }

    fn canonicalize_extracted_fixture_crate_id(
        raw_stable_crate_id: &mut Option<u64>,
        stable_crate_id: &mut u64,
    ) {
        if let Some(expected) = *raw_stable_crate_id {
            assert_eq!(
                *stable_crate_id, expected,
                "extracted fixture contains multiple authenticated crate identities; \
                 do not collapse them into one snapshot namespace"
            );
        } else {
            *raw_stable_crate_id = Some(*stable_crate_id);
        }
        *stable_crate_id = EXTRACTED_FIXTURE_STABLE_CRATE_ID;
    }

    #[test]
    fn extracted_fixture_identity_canonicalization_preserves_exact_callee_components() {
        let mut observed = None;
        let mut identity = trust_types::CalleeIdentity {
            stable_crate_id: 17,
            def_index: 29,
            substs_digest: [31, 37],
        };

        canonicalize_extracted_fixture_crate_id(&mut observed, &mut identity.stable_crate_id);

        assert_eq!(observed, Some(17));
        assert_eq!(identity.stable_crate_id, EXTRACTED_FIXTURE_STABLE_CRATE_ID);
        assert_eq!(identity.def_index, 29);
        assert_eq!(identity.substs_digest, [31, 37]);
    }

    #[test]
    #[should_panic(expected = "multiple authenticated crate identities")]
    fn extracted_fixture_identity_canonicalization_refuses_multiple_crates() {
        let mut observed = Some(17);
        let mut foreign_identity = trust_types::CalleeIdentity {
            stable_crate_id: 19,
            def_index: 29,
            substs_digest: [31, 37],
        };

        canonicalize_extracted_fixture_crate_id(
            &mut observed,
            &mut foreign_identity.stable_crate_id,
        );
    }

    #[test]
    fn extracted_fixture_identity_canonicalization_covers_keys_and_tail_calls() {
        let original = extract_mirror_fixture_bodies();
        let original_json = serde_json::to_string(&original).unwrap();
        for tail in [false, true] {
            for retain_identity in [false, true] {
                let mut functions = original.clone();
                for function in functions.values_mut() {
                    for block in &mut function.body.blocks {
                        if let Terminator::Call {
                            func,
                            args,
                            span,
                            atomic,
                            is_foreign,
                            is_unsafe_sig,
                            callee_identity,
                            callee_key,
                            ..
                        } = block.terminator.clone()
                        {
                            if tail {
                                block.terminator = Terminator::TailCall {
                                    func,
                                    args,
                                    span,
                                    atomic,
                                    is_foreign,
                                    is_unsafe_sig,
                                    callee_identity,
                                    callee_key,
                                };
                            }
                        }
                        match &mut block.terminator {
                            Terminator::Call { callee_identity, .. }
                            | Terminator::TailCall { callee_identity, .. } => {
                                if !retain_identity {
                                    *callee_identity = None;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                let canonical = canonicalize_extracted_fixture_callee_ids(&functions);
                let mut observed_keys = 0;
                for (name, function) in &functions {
                    for (before, after) in
                        function.body.blocks.iter().zip(&canonical[name].body.blocks)
                    {
                        let mut expected = before.terminator.clone();
                        match &mut expected {
                            Terminator::Call { callee_identity, callee_key, .. }
                            | Terminator::TailCall { callee_identity, callee_key, .. } => {
                                if let Some(identity) = callee_identity {
                                    identity.stable_crate_id = EXTRACTED_FIXTURE_STABLE_CRATE_ID;
                                }
                                let key = callee_key.as_mut().expect("mirror calls carry a key");
                                key.stable_crate_id = EXTRACTED_FIXTURE_STABLE_CRATE_ID;
                                observed_keys += 1;
                            }
                            _ => {}
                        }
                        assert_eq!(
                            serde_json::to_value(&after.terminator).unwrap(),
                            serde_json::to_value(&expected).unwrap()
                        );
                    }
                }
                assert!(observed_keys > 0);
            }
        }
        assert_eq!(serde_json::to_string(&original).unwrap(), original_json);
    }

    #[test]
    #[should_panic(expected = "multiple authenticated crate identities")]
    fn extracted_fixture_identity_canonicalization_refuses_disagreeing_key() {
        let mut functions = extract_mirror_fixture_bodies();
        let mut changed = false;
        for function in functions.values_mut() {
            for block in &mut function.body.blocks {
                if let Terminator::Call {
                    callee_identity: Some(identity),
                    callee_key: Some(key),
                    ..
                } = &mut block.terminator
                {
                    key.stable_crate_id = identity.stable_crate_id.wrapping_add(1);
                    changed = true;
                }
            }
        }
        assert!(changed, "mirror fixture must exercise the disagreement");
        canonicalize_extracted_fixture_callee_ids(&functions);
    }

    /// Canonical serialization of an extraction run: pretty JSON of the
    /// name -> `VerifiableFunction` map (BTreeMap: key order is stable;
    /// struct fields serialize in declaration order), trailing newline.
    fn serialize_extracted_functions(functions: &BTreeMap<String, VerifiableFunction>) -> String {
        let canonical = canonicalize_extracted_fixture_callee_ids(functions);
        let mut json = serde_json::to_string_pretty(&canonical)
            .expect("VerifiableFunction serialization is infallible");
        json.push('\n');
        json
    }

    /// The drift gate: the fresh in-process extraction must match the
    /// committed artifact byte-for-byte. With `TRUST_UPDATE_EXTRACTED_FIXTURES=1`
    /// the committed artifact is (re)written instead.
    fn assert_matches_committed_artifact(
        artifact: &str,
        functions: &BTreeMap<String, VerifiableFunction>,
    ) {
        let json = serialize_extracted_functions(functions);
        let path = extracted_artifacts_dir().join(artifact);
        if std::env::var_os("TRUST_UPDATE_EXTRACTED_FIXTURES").is_some() {
            std::fs::create_dir_all(extracted_artifacts_dir()).expect("create fixtures/extracted");
            std::fs::write(&path, &json)
                .unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
            eprintln!("regenerated extracted artifact {}", path.display());
            return;
        }
        let committed = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "missing committed extracted artifact {} ({e}). The artifact is \
                 REGENERATED, never hand-edited: rerun this test with \
                 TRUST_UPDATE_EXTRACTED_FIXTURES=1 and commit the JSON.",
                path.display()
            )
        });
        assert!(
            committed == json,
            "extracted artifact DRIFT: {} no longer matches the live extractor's \
             output. If the extractor change is intentional, regenerate with \
             TRUST_UPDATE_EXTRACTED_FIXTURES=1 and commit the JSON together with \
             the change (the integration e2e tests consume this artifact).",
            path.display()
        );
    }

    /// WALL C scaled to MUTUAL SCCs — compile the mutual ring fixture and
    /// extract every free function's real MIR body as a `VerifiableFunction`.
    /// Same invocation as the mirror fixture.
    fn extract_mutual_fixture_bodies() -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = MutualBodyCallbacks { functions: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            MUTUAL_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "clean_kernel".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ainternal_features".to_string(),
        ];
        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile clean_kernel mutual fixture");
        callbacks.functions
    }

    /// Lever A step 3 (FAITHFULNESS of the VC-gen INPUT): the real extracted MIR
    /// body of `build_sort(l) = ExprKind::Sort(l)` is exactly the
    /// `Rvalue::Aggregate(Adt { variant = Sort, .. }, [l])` over a `Ty::Datatype`
    /// dest that `trust-vcgen::datatype_functional` models as `Ctor("Sort",[l])`.
    /// This closes the gap between the hand-built representatives in the
    /// trust-vcgen unit tests and what the extractor actually produces.
    #[test]
    fn real_mir_sort_arm_body_is_datatype_aggregate() {
        let bodies = extract_expr_fixture_bodies();
        let f = bodies
            .get("build_sort")
            .unwrap_or_else(|| panic!("build_sort not extracted; saw {:?}", bodies.keys()));

        // The return type is the modeled ExprKind datatype (step 5), not Unsupported.
        assert!(
            f.body.return_ty.is_datatype(),
            "build_sort return type must be a modeled datatype, got {:?}",
            f.body.return_ty
        );

        // Find the enum-variant construction: `_x = ExprKind::Sort(l)`.
        let mut matched = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign {
                    place,
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, ops),
                    ..
                } = stmt
                else {
                    continue;
                };
                let dest_ty = f.body.locals.iter().find(|d| d.index == place.local).map(|d| &d.ty);
                if let Some(Ty::Datatype { name, variants }) = dest_ty {
                    if name.ends_with("ExprKind") {
                        matched = Some((*variant, variants.clone(), ops.len()));
                    }
                }
            }
        }

        let (variant, variants, n_ops) = matched
            .expect("build_sort must lower to an Aggregate(Adt) constructing an ExprKind variant");
        let (ctor, fields) = &variants[variant];
        assert_eq!(ctor, "Sort", "the constructed variant is Sort");
        assert_eq!(fields.len(), 1, "Sort has one (Level) field");
        assert_eq!(n_ops, 1, "the Aggregate carries exactly the single level operand");
    }

    /// WALL C (FAITHFULNESS of the recursive VC-gen INPUT): the real extracted
    /// MIR of the SELF-recursive `mirror : &Level -> Level` has exactly the
    /// shape `trust-vcgen::recursive_datatype_functional` walks (the
    /// `extracted_mirror_func` transcriptions in trust-vcgen's unit tests
    /// mirror it; trust-integration-tests' `recursive_datatype_functional_e2e`
    /// consumes the LITERAL extraction via the drift-gated committed artifact,
    /// see `extracted_mirror_artifact_matches_committed`):
    ///   * the 2-variant `level::Level` lowers to `Ty::Datatype` (return slot),
    ///     the parameter to `Ref { Datatype }`;
    ///   * a `Discriminant((*_1))` + `SwitchInt` covering BOTH variant tags,
    ///     `otherwise -> Unreachable` (exhaustive match);
    ///   * the Zero arm builds `Aggregate(Adt { variant: 0 }, [])` into `_0`;
    ///   * the Succ arm reads the payload `((*_1 as Succ).0)`, SELF-CALLS
    ///     `mirror` on it (the recursive occurrence the VC lane replaces with
    ///     the IH variable), and builds `Aggregate(Adt { variant: 1 }, [ptr])`
    ///     from the call result (through the `&m as *const _` AddressOf).
    #[test]
    fn real_mir_recursive_mirror_body_shape() {
        let bodies = extract_mirror_fixture_bodies();
        let f = bodies
            .get("mirror")
            .unwrap_or_else(|| panic!("mirror not extracted; saw {:?}", bodies.keys()));

        // Return slot: the modeled 2-variant Level datatype.
        // Trust: through `datatype_defs` — `Level` is self-recursive, so it is a
        // canonical cut point and its return slot is a by-name marker.
        let (name, variants) = resolve_datatype(&f.body.return_ty, &f.body.datatype_defs);
        assert_eq!(name, "clean_kernel::level::Level");
        assert_eq!(
            variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
            vec![("Zero", 0), ("Succ", 1)],
            "the fixture Level slice is Zero | Succ(Level)"
        );
        // Parameter: a reference to the same datatype (the model peels it).
        assert_eq!(f.body.arg_count, 1);
        let param_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
        assert!(
            matches!(param_ty, Ty::Ref { inner, .. } if inner.is_datatype()),
            "param must be &Level, got {param_ty:?}"
        );

        // The match: Discriminant((*_1)) driving a SwitchInt over BOTH tags,
        // with the exhaustive-match otherwise -> Unreachable.
        let mut saw_discr_on_param = false;
        let mut switch = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::Discriminant(p), .. } = stmt {
                    assert_eq!(p.local, 1, "the discriminant is read off the parameter");
                    assert_eq!(p.projections, vec![Projection::Deref]);
                    saw_discr_on_param = true;
                }
            }
            if let Terminator::SwitchInt { targets, otherwise, .. } = &block.terminator {
                switch = Some((targets.clone(), *otherwise));
            }
        }
        assert!(saw_discr_on_param, "must read discriminant((*_1))");
        let (targets, otherwise) = switch.expect("mirror must lower to a SwitchInt match");
        let mut tags: Vec<u128> = targets.iter().map(|(t, _)| *t).collect();
        tags.sort_unstable();
        assert_eq!(tags, vec![0, 1], "the switch must cover both constructor tags");
        let otherwise_block =
            f.body.blocks.iter().find(|b| b.id == otherwise).expect("otherwise block");
        assert!(
            matches!(otherwise_block.terminator, Terminator::Unreachable),
            "exhaustive match: otherwise must be Unreachable, got {:?}",
            otherwise_block.terminator
        );

        // The SELF-recursive call, fed by the Succ payload read.
        let mut saw_payload_read = false;
        let mut self_call = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p)), .. } = stmt {
                    if p.local == 1
                        && p.projections
                            == vec![
                                Projection::Deref,
                                Projection::Downcast(1),
                                Projection::Field(0),
                            ]
                    {
                        saw_payload_read = true;
                    }
                }
            }
            if let Terminator::Call { func: callee, args, target, .. } = &block.terminator {
                if callee == "clean_kernel::mirror" {
                    assert_eq!(args.len(), 1, "mirror takes one argument");
                    assert!(target.is_some(), "the recursive call returns normally");
                    self_call = Some(());
                }
            }
        }
        assert!(saw_payload_read, "the Succ arm must read the payload ((*_1 as Succ).0)");
        assert!(self_call.is_some(), "mirror must contain the SELF-recursive call");

        // Both constructor arms build `_0` as datatype aggregates: the Zero arm
        // a nullary variant-0, the Succ arm a unary variant-1 from the call
        // result (via AddressOf).
        let mut zero_arm = false;
        let mut succ_arm = false;
        let mut saw_addressof = false;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, ops),
                        ..
                    } if place.local == 0 && place.projections.is_empty() => match variant {
                        0 => {
                            assert!(ops.is_empty(), "Zero is nullary");
                            zero_arm = true;
                        }
                        1 => {
                            assert_eq!(ops.len(), 1, "Succ carries one payload");
                            succ_arm = true;
                        }
                        v => panic!("unexpected variant {v} constructed into _0"),
                    },
                    Statement::Assign { rvalue: Rvalue::AddressOf(_, p), .. } => {
                        // `&m as *const Level` — the address of the recursive
                        // call's result local.
                        assert!(p.projections.is_empty());
                        saw_addressof = true;
                    }
                    _ => {}
                }
            }
        }
        assert!(zero_arm, "the Zero arm must build Aggregate(variant 0, [])");
        assert!(succ_arm, "the Succ arm must build Aggregate(variant 1, [result ptr])");
        assert!(saw_addressof, "the Succ arm coerces the call result via AddressOf");
    }

    /// WALL C SCALED TO MUTUAL SCCs (FAITHFULNESS of the mutual VC-gen INPUT):
    /// the real extracted MIR of the 3-function ring `fm -> gm -> hm -> fm`
    /// has exactly the fuel-indexed cluster shape
    /// `trust-vcgen::mutual_recursive_datatype_functional` walks (the
    /// `ring_member` transcriptions in trust-vcgen's unit tests mirror it;
    /// trust-integration-tests' `mutual_recursive_datatype_functional_e2e`
    /// consumes the LITERAL extraction via the drift-gated committed artifact,
    /// see `extracted_mutual_artifact_matches_committed`):
    ///   * the fuel parameter is `&level::Level` with the nat-shaped 2-variant
    ///     slice (`Zero` nullary, `Succ` unary-recursive) and the payload
    ///     parameter/return is the 2-variant `expr::kind::ExprKind` datatype;
    ///   * the FIRST match is on the FUEL discriminant (`(*_1)`), the payload
    ///     match on `(*_2)` under BOTH fuel arms, exhaustive-otherwise
    ///     `Unreachable`;
    ///   * the Zero (base) subtree contains NO call — the identity rebuild
    ///     reads the `B` payload and rebuilds `Aggregate(variant 1, ..)`;
    ///   * the Succ (step) subtree reads the smaller fuel `((*_1 as Succ).0)`,
    ///     reads the `B` payload, and calls the NEXT ring member with TWO
    ///     arguments (fuel first) — the cross-member cluster edge the mutual
    ///     lane turns into the `[calls=..]`-tagged IH atom;
    ///   * the call-graph over the trio is one genuine SCC of size 3.
    #[test]
    fn real_mir_mutual_cluster_body_shape() {
        let bodies = extract_mutual_fixture_bodies();
        let ring = [("fm", "gm"), ("gm", "hm"), ("hm", "fm")];
        for (name, next) in ring {
            let f = bodies
                .get(name)
                .unwrap_or_else(|| panic!("{name} not extracted; saw {:?}", bodies.keys()));

            // Return slot + payload parameter: the modeled 2-variant ExprKind.
            // Trust: through `datatype_defs` — a self-recursive return type is a
            // canonical cut point, so this slot is a by-name marker.
            let (ret_name, variants) = resolve_datatype(&f.body.return_ty, &f.body.datatype_defs);
            assert_eq!(ret_name, "clean_kernel::expr::kind::ExprKind");
            assert_eq!(
                variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("A", 0), ("B", 1)],
                "the payload slice is A | B(ExprKind)"
            );
            assert_eq!(f.body.arg_count, 2, "{name} takes (fuel, payload)");
            let fuel_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
            let Ty::Ref { inner, .. } = fuel_ty else {
                panic!("{name} fuel param must be &Level, got {fuel_ty:?}");
            };
            // Trust: through `datatype_defs` — the nat-shaped fuel type is
            // recursive, hence a cut point, hence a marker at this occurrence.
            let (fuel_name, fuel_variants) =
                resolve_datatype(inner.as_ref(), &f.body.datatype_defs);
            assert_eq!(fuel_name, "clean_kernel::level::Level");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Zero", 0), ("Succ", 1)],
                "the fuel index is nat-shaped"
            );
            let payload_ty = &f.body.locals.iter().find(|d| d.index == 2).expect("param _2").ty;
            assert!(
                matches!(payload_ty, Ty::Ref { inner, .. } if inner.is_datatype()),
                "{name} payload param must be &ExprKind, got {payload_ty:?}"
            );

            // Discriminant reads: the fuel match off `(*_1)` and the payload
            // match(es) off `(*_2)`; every switch's otherwise is Unreachable.
            let mut disc_locals: std::collections::HashMap<usize, usize> =
                std::collections::HashMap::new();
            for block in &f.body.blocks {
                for stmt in &block.stmts {
                    if let Statement::Assign { place, rvalue: Rvalue::Discriminant(p), .. } = stmt {
                        assert_eq!(p.projections, vec![Projection::Deref]);
                        disc_locals.insert(place.local, p.local);
                    }
                }
            }
            assert!(
                disc_locals.values().any(|&param| param == 1),
                "{name} must read discriminant((*_1)) — the fuel match"
            );
            assert!(
                disc_locals.values().any(|&param| param == 2),
                "{name} must read discriminant((*_2)) — the payload match"
            );
            let mut first_switch_param = None;
            for block in &f.body.blocks {
                if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator {
                    let local = match discr {
                        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
                        other => panic!("{name} switch discr must be a plain local, got {other:?}"),
                    };
                    let param = disc_locals
                        .get(&local)
                        .unwrap_or_else(|| panic!("{name} switch on unread discriminant"));
                    if first_switch_param.is_none() {
                        first_switch_param = Some(*param);
                    }
                    let mut tags: Vec<u128> = targets.iter().map(|(t, _)| *t).collect();
                    tags.sort_unstable();
                    assert_eq!(tags, vec![0, 1], "{name} switches cover both constructor tags");
                    let ob = f.body.blocks.iter().find(|b| b.id == *otherwise).expect("otherwise");
                    assert!(
                        matches!(ob.terminator, Terminator::Unreachable),
                        "{name}: exhaustive match otherwise must be Unreachable"
                    );
                }
            }
            assert_eq!(
                first_switch_param,
                Some(1),
                "{name}: the FIRST switch (entry block) must match the FUEL parameter"
            );

            // The smaller-fuel read and the cross-member call (fuel first).
            let mut saw_fuel_payload_read = false;
            let mut cluster_call = None;
            for block in &f.body.blocks {
                for stmt in &block.stmts {
                    if let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p)), .. } = stmt {
                        if p.local == 1
                            && p.projections
                                == vec![
                                    Projection::Deref,
                                    Projection::Downcast(1),
                                    Projection::Field(0),
                                ]
                        {
                            saw_fuel_payload_read = true;
                        }
                    }
                }
                if let Terminator::Call { func: callee, args, target, .. } = &block.terminator {
                    assert_eq!(
                        callee,
                        &format!("clean_kernel::{next}"),
                        "{name}'s only call is its ring successor"
                    );
                    assert_eq!(args.len(), 2, "cluster calls pass (fuel, payload)");
                    assert!(target.is_some(), "the cluster call returns normally");
                    cluster_call = Some(());
                }
            }
            assert!(
                saw_fuel_payload_read,
                "{name}: the Succ arm must read the smaller fuel ((*_1 as Succ).0)"
            );
            assert!(cluster_call.is_some(), "{name} must contain the cross-member call");
        }

        // The trio really is ONE strongly connected component of size 3: the
        // extracted call edges form exactly the ring fm -> gm -> hm -> fm.
        let mut edges: Vec<(String, String)> = Vec::new();
        for (name, _) in ring {
            for block in &bodies[name].body.blocks {
                if let Terminator::Call { func: callee, .. } = &block.terminator {
                    edges.push((name.to_string(), callee.clone()));
                }
            }
        }
        edges.sort();
        edges.dedup();
        assert_eq!(
            edges,
            vec![
                ("fm".to_string(), "clean_kernel::gm".to_string()),
                ("gm".to_string(), "clean_kernel::hm".to_string()),
                ("hm".to_string(), "clean_kernel::fm".to_string()),
            ],
            "the extracted cluster is the single 3-cycle SCC"
        );
    }

    /// EXTRACTION SERIALIZATION (shape sanity): the literal-cluster fixture
    /// extracts with the shapes its consumers rely on — the payload is the
    /// FULL 5-constructor `level::Level` (multi-IH `Max`/`IMax`, opaque
    /// `Param(Name)`), the fuel is the nat-shaped 2-constructor
    /// `expr::kind::ExprKind` slice, the model cluster {fm, gm} and the
    /// reference cluster {fr, gr} are genuine 2-SCCs, the reference members'
    /// fuel-Z arm is a DIRECT payload return (no per-ctor rebuild), and
    /// `gm_wrong` differs from the true bodies exactly by rebuilding Max in
    /// an IMax step arm. The full byte-level pin is the committed artifact
    /// (see `extracted_literal_cluster_artifact_matches_committed`).
    #[test]
    fn real_mir_literal_cluster_body_shape() {
        let bodies = extract_literal_cluster_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["fm", "fr", "gm", "gm_wrong", "gr"],
            "the five cluster functions extract"
        );

        for (name, f) in &bodies {
            // Return slot + payload parameter: the FULL modeled Level.
            // Trust: through `datatype_defs` — a self-recursive return type is a
            // canonical cut point, so this slot is a by-name marker.
            let (ret_name, variants) = resolve_datatype(&f.body.return_ty, &f.body.datatype_defs);
            assert_eq!(ret_name, "clean_kernel::level::Level");
            assert_eq!(
                variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Zero", 0), ("Succ", 1), ("Max", 2), ("IMax", 2), ("Param", 1)],
                "{name}: the payload is the full Level slice"
            );
            // The Param field is the opaque Name (a by-name datatype ref).
            let param_field = &variants[4].1[0].1;
            assert!(
                matches!(
                    param_field,
                    Ty::Datatype { name, variants }
                        if name == "clean_kernel::name::Name" && variants.is_empty()
                ),
                "{name}: Param carries the opaque Name ref, got {param_field:?}"
            );
            // Fuel parameter: the nat-shaped gated ExprKind slice.
            assert_eq!(f.body.arg_count, 2, "{name} takes (fuel, payload)");
            let fuel_ty = &f.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
            let Ty::Ref { inner, .. } = fuel_ty else {
                panic!("{name} fuel param must be &ExprKind, got {fuel_ty:?}");
            };
            // Trust: through `datatype_defs` — the nat-shaped fuel type is
            // recursive, hence a cut point, hence a marker at this occurrence.
            let (fuel_name, fuel_variants) =
                resolve_datatype(inner.as_ref(), &f.body.datatype_defs);
            assert_eq!(fuel_name, "clean_kernel::expr::kind::ExprKind");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Z", 0), ("S", 1)],
                "{name}: the fuel index is nat-shaped"
            );
        }

        // Call edges: the model 2-SCC, the wrong twin's edge into it, and the
        // reference 2-SCC.
        let mut edges: Vec<(String, String)> = Vec::new();
        for (name, f) in &bodies {
            for block in &f.body.blocks {
                if let Terminator::Call { func: callee, args, .. } = &block.terminator {
                    assert_eq!(args.len(), 2, "{name}: cluster calls pass (fuel, payload)");
                    edges.push((name.clone(), callee.clone()));
                }
            }
        }
        edges.sort();
        edges.dedup();
        assert_eq!(
            edges,
            vec![
                ("fm".to_string(), "clean_kernel::gm".to_string()),
                ("fr".to_string(), "clean_kernel::gr".to_string()),
                ("gm".to_string(), "clean_kernel::fm".to_string()),
                ("gm_wrong".to_string(), "clean_kernel::fm".to_string()),
                ("gr".to_string(), "clean_kernel::fr".to_string()),
            ],
            "model SCC {{fm,gm}}, reference SCC {{fr,gr}}, gm_wrong -> fm"
        );

        // Reference members: the fuel-Z arm is a DIRECT `copy (*_2)` return
        // into _0 — no per-constructor rebuild (the model/reference folds are
        // genuinely different).
        for name in ["fr", "gr"] {
            let f = &bodies[name];
            let direct_base = f.body.blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(
                        s,
                        Statement::Assign { place, rvalue: Rvalue::Use(Operand::Copy(p)), .. }
                            if place.local == 0
                                && place.projections.is_empty()
                                && p.local == 2
                                && p.projections == vec![Projection::Deref]
                    )
                })
            });
            assert!(direct_base, "{name}: the fuel-Z arm returns the payload directly");
        }

        // gm vs gm_wrong: same everything except ONE aggregate variant — the
        // IMax step arm's rebuild (IMax=3 in gm, Max=2 in gm_wrong).
        let rebuild_variants = |f: &VerifiableFunction| -> Vec<usize> {
            f.body
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .filter_map(|s| match s {
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _),
                        ..
                    } if place.local == 0 && place.projections.is_empty() => Some(*variant),
                    _ => None,
                })
                .collect()
        };
        let gm_variants = rebuild_variants(&bodies["gm"]);
        let wrong_variants = rebuild_variants(&bodies["gm_wrong"]);
        assert_eq!(gm_variants.len(), wrong_variants.len());
        let diffs: Vec<(usize, usize)> = gm_variants
            .iter()
            .zip(&wrong_variants)
            .filter(|(a, b)| a != b)
            .map(|(a, b)| (*a, *b))
            .collect();
        assert_eq!(
            diffs,
            vec![(3, 2)],
            "gm_wrong differs from gm exactly by rebuilding Max (2) where gm rebuilds IMax (3)"
        );
    }

    /// Drift gate: the committed expr-fixture artifact (`build_sort`,
    /// `build_sort_expr`) is byte-identical to the live extraction.
    #[test]
    fn extracted_expr_artifact_matches_committed() {
        let bodies = extract_expr_fixture_bodies();
        assert!(bodies.contains_key("build_sort"), "saw {:?}", bodies.keys());
        assert_matches_committed_artifact("expr_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed mirror artifact (the WALL C self-recursive
    /// `mirror`, consumed by `recursive_datatype_functional_e2e`) is
    /// byte-identical to the live extraction.
    #[test]
    fn extracted_mirror_artifact_matches_committed() {
        let bodies = extract_mirror_fixture_bodies();
        assert!(bodies.contains_key("mirror"), "saw {:?}", bodies.keys());
        assert_matches_committed_artifact("mirror_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed mutual-ring artifact (fm/gm/hm, consumed by
    /// `mutual_recursive_datatype_functional_e2e`) is byte-identical to the
    /// live extraction.
    #[test]
    fn extracted_mutual_artifact_matches_committed() {
        let bodies = extract_mutual_fixture_bodies();
        assert_eq!(bodies.keys().cloned().collect::<Vec<_>>(), vec!["fm", "gm", "hm"]);
        assert_matches_committed_artifact("mutual_fixture_functions.json", &bodies);
    }

    /// Drift gate: the committed literal-cluster artifact (fm/gm/gm_wrong/
    /// fr/gr, consumed by `mutual_literal_cluster_e2e`) is byte-identical to
    /// the live extraction.
    #[test]
    fn extracted_literal_cluster_artifact_matches_committed() {
        let bodies = extract_literal_cluster_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["fm", "fr", "gm", "gm_wrong", "gr"]
        );
        assert_matches_committed_artifact("literal_cluster_fixture_functions.json", &bodies);
    }

    /// The canonical cluster spec for the cell-counter fixture: the
    /// cell-mediated model {fm, gm}, the hand-threaded reference {fr, gr}, and
    /// the accessor callee names.
    fn cell_counter_spec() -> crate::cell_threading::CellThreadingSpec {
        crate::cell_threading::CellThreadingSpec {
            members: vec!["fm".to_string(), "gm".to_string()],
            references: vec!["fr".to_string(), "gr".to_string()],
            get_fn: "cell_get".to_string(),
            set_fn: "cell_set".to_string(),
        }
    }

    /// INTERIOR-MUTABILITY GAP — the Cell→threading transform on the LITERAL
    /// extracted MIR. Extract the cell-mediated cluster and lower it with
    /// `thread_cell_state`, then assert the output is in the
    /// `threaded_budget_functional` lane grammar: `(&Fuel, E) -> Res`, a fuel
    /// switch whose Z arm is the pinned exhaustion `Mk(*fuel, *e)`, and cluster
    /// calls whose fuel argument is the current cell state (`&(*_9)` for the
    /// first call, a reborrow of the previous call's remainder `_.0` for the
    /// threaded second call). The negative control (`fm_leak`, which passes the
    /// holder to an out-of-grammar callee) must fail closed.
    #[test]
    fn real_mir_cell_counter_threads_to_lane_shape() {
        use crate::cell_threading::thread_cell_state;
        let bodies = extract_cell_counter_fixture_bodies();
        assert_eq!(
            bodies.keys().cloned().collect::<Vec<_>>(),
            vec!["cell_get", "cell_set", "fm", "fm_leak", "fr", "gm", "gr", "leak"],
            "the cell fixture extracts the accessors, model, negative, and reference"
        );

        let threaded = thread_cell_state(&bodies, &cell_counter_spec())
            .expect("the cell-mediated cluster lowers to the threaded shape");
        assert_eq!(threaded.keys().cloned().collect::<Vec<_>>(), vec!["fm", "fr", "gm", "gr"]);

        // The result-pair datatype `Res = Mk(Fuel, E)`, derived from the
        // reference return type by normalization.
        let res_dt = &threaded["fr"].body.return_ty;
        let Ty::Datatype { name: res_name, variants: res_variants } = res_dt else {
            panic!("Res must normalize to a datatype, got {res_dt:?}");
        };
        assert_eq!(res_name, "clean_kernel::res::Res");
        assert_eq!(res_variants.len(), 1, "the pair has one constructor");
        assert_eq!(res_variants[0].0, "Mk");

        for name in ["fm", "gm"] {
            let f = &threaded[name];
            // Threaded signature: `_1: &Fuel`, `_0: Res`.
            assert_eq!(f.body.arg_count, 2);
            assert_eq!(f.body.return_ty, *res_dt, "{name} now returns the result pair");
            let fuel_param = &f.body.locals.iter().find(|l| l.index == 1).unwrap().ty;
            let Ty::Ref { inner, .. } = fuel_param else {
                panic!("{name} param _1 must be &Fuel, got {fuel_param:?}");
            };
            // Trust: through `datatype_defs` — the nat-shaped fuel type is
            // recursive, hence a cut point, hence a marker at this occurrence.
            let (fuel_name, fuel_variants) =
                resolve_datatype(inner.as_ref(), &f.body.datatype_defs);
            assert_eq!(fuel_name, "clean_kernel::fuel::Fuel");
            assert_eq!(
                fuel_variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
                vec![("Z", 0), ("S", 1)],
                "{name}: the fuel index is nat-shaped"
            );

            // NO surviving cell mechanism: no call to a cell accessor, and `_1`
            // is never an assignment destination (it is the read-only fuel).
            for b in &f.body.blocks {
                if let Terminator::Call { func: callee, .. } = &b.terminator {
                    assert!(
                        callee != "cell_get" && callee != "cell_set",
                        "{name}: accessor calls are lowered away, saw {callee}"
                    );
                }
                for s in &b.stmts {
                    if let Statement::Assign { place, .. } = s {
                        assert_ne!(place.local, 1, "{name}: the fuel param is never written");
                    }
                }
            }

            // Every return site produces the result pair `_0 = Mk(_, _)`.
            let returns_pair = f.body.blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(s, Statement::Assign {
                        place,
                        rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops),
                        ..
                    } if place.local == 0
                        && name == "clean_kernel::res::Res"
                        && ops.len() == 2)
                })
            });
            assert!(returns_pair, "{name}: return sites are wrapped into Mk(rem, payload)");

            // The cluster calls are threaded: every remaining Call targets the
            // sibling member and passes a fuel-typed first argument.
            let cluster_calls = f
                .body
                .blocks
                .iter()
                .filter_map(|b| match &b.terminator {
                    Terminator::Call { func: callee, args, .. } => {
                        Some((callee.clone(), args.len()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert!(
                !cluster_calls.is_empty()
                    && cluster_calls
                        .iter()
                        .all(|(c, argc)| { (c == "fm" || c == "gm") && *argc == 2 }),
                "{name}: all surviving calls are 2-arg cluster calls, saw {cluster_calls:?}"
            );
        }
    }

    /// INTERIOR-MUTABILITY GAP negative — the transform FAILS CLOSED when the
    /// holder escapes the accessor/cluster-call grammar. Threading a spec that
    /// includes `fm_leak` (which passes `tc` to the out-of-grammar `leak`)
    /// yields `None`.
    #[test]
    fn cell_threading_rejects_holder_escape() {
        use crate::cell_threading::{CellThreadingSpec, thread_cell_state};
        let bodies = extract_cell_counter_fixture_bodies();
        let escaping = CellThreadingSpec {
            members: vec!["fm".to_string(), "gm".to_string(), "fm_leak".to_string()],
            references: vec!["fr".to_string(), "gr".to_string()],
            get_fn: "cell_get".to_string(),
            set_fn: "cell_set".to_string(),
        };
        assert!(
            thread_cell_state(&bodies, &escaping).is_none(),
            "a holder that escapes to an out-of-grammar callee must fail closed"
        );
    }

    /// Drift gate: the committed THREADED artifact (`fm/fr/gm/gr` in the
    /// threaded-budget lane shape, consumed by `cell_threading_e2e`) is
    /// byte-identical to `thread_cell_state` applied to the live extraction.
    #[test]
    fn extracted_cell_threaded_artifact_matches_committed() {
        use crate::cell_threading::thread_cell_state;
        let bodies = extract_cell_counter_fixture_bodies();
        let threaded = thread_cell_state(&bodies, &cell_counter_spec())
            .expect("the cell-mediated cluster lowers to the threaded shape");
        assert_eq!(threaded.keys().cloned().collect::<Vec<_>>(), vec!["fm", "fr", "gm", "gr"]);
        assert_matches_committed_artifact("cell_threaded_functions.json", &threaded);
    }

    /// Structural node count of a lowered `Ty`, short-circuited at `cap` so a
    /// pathological (blown-up) tree costs O(cap) to measure rather than hanging.
    /// Used by the step-5 tests to prove the by-name refs keep extraction BOUNDED.
    fn ty_total_node_count(ty: &Ty, cap: usize) -> usize {
        fn go(ty: &Ty, cap: usize, acc: &mut usize) {
            if *acc >= cap {
                return;
            }
            *acc += 1;
            match ty {
                Ty::Datatype { variants, .. } => {
                    for (_, fs) in variants {
                        for (_, t) in fs {
                            go(t, cap, acc);
                        }
                    }
                }
                Ty::Adt { fields, variants, .. } => {
                    for (_, t) in fields {
                        go(t, cap, acc);
                    }
                    for v in variants {
                        for (_, t) in &v.fields {
                            go(t, cap, acc);
                        }
                    }
                }
                Ty::Ref { inner, .. } => go(inner, cap, acc),
                Ty::RawPtr { pointee, .. } => go(pointee, cap, acc),
                Ty::Tuple(ts) => ts.iter().for_each(|t| go(t, cap, acc)),
                _ => {}
            }
        }
        let mut acc = 0;
        go(ty, cap, &mut acc);
        acc
    }

    fn direct_call_symbol_names<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<String> {
        let typing_env = body.typing_env(tcx);

        body.basic_blocks
            .iter()
            .filter_map(|bb| match &bb.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => match func {
                    mir::Operand::Constant(const_op) => match const_op.const_.ty().kind() {
                        rustc_middle::ty::TyKind::FnDef(def_id, generic_args) => {
                            if crate::tuple_layouts::resolution_may_reenter(
                                tcx,
                                *def_id,
                                generic_args.skip_binder(),
                            ) {
                                return None;
                            }
                            rustc_middle::ty::Instance::try_resolve(
                                tcx,
                                typing_env,
                                *def_id,
                                generic_args.skip_binder(),
                            )
                            .ok()
                            .flatten()
                            .map(|instance| tcx.symbol_name(instance).name.to_string())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    fn direct_call_func_types<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<Ty> {
        // Trust: M6 rung-7 sweep — use `body`'s own `typing_env` instead of the
        // plain env-less `convert_ty` (mirrors `direct_call_symbol_names` above,
        // which already computes the same `body.typing_env(tcx)`).
        let typing_env = body.typing_env(tcx);
        body.basic_blocks
            .iter()
            .filter_map(|bb| match &bb.terminator().kind {
                mir::TerminatorKind::Call { func, .. } => match func {
                    mir::Operand::Constant(const_op)
                        if matches!(
                            const_op.const_.ty().kind(),
                            rustc_middle::ty::TyKind::FnDef(..)
                        ) =>
                    {
                        Some(ty_convert::convert_ty_in_env(tcx, typing_env, const_op.const_.ty()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    fn extracted_call_targets(func: &VerifiableFunction) -> Vec<String> {
        func.body
            .blocks
            .iter()
            .filter_map(|bb| match &bb.terminator {
                Terminator::Call { func, .. } => Some(func.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn codegen_fidelity_validator_recursively_rejects_placeholders() {
        let nested = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Tuple(vec![
                Ty::u32(),
                Ty::Unsupported { kind: "test".to_string(), detail: "nested".to_string() },
            ])),
        };
        assert!(
            codegen_ty_issue(&nested, "test type").is_some_and(|detail| detail.contains("nested")),
            "nested unsupported types must not escape the codegen gate"
        );
        assert!(codegen_projection_issue(&Projection::OpaqueCast(Ty::u32())).is_some());
        assert!(codegen_const_issue(&ConstValue::opaque_const()).is_some());
        assert!(
            codegen_ty_issue(&Ty::Int { width: 128, signed: true }, "signed adversary")
                .is_some_and(|detail| detail.contains("128-bit integer"))
        );
        assert!(
            codegen_ty_issue(&Ty::Bv(128), "bitvector adversary")
                .is_some_and(|detail| detail.contains("128-bit bitvector"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Int(1))
                .is_some_and(|detail| detail.contains("source bit width"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Uint(1, 128))
                .is_some_and(|detail| detail.contains("128-bit unsigned"))
        );
        assert!(
            codegen_const_issue(&ConstValue::Uint(256, 8))
                .is_some_and(|detail| detail.contains("does not fit"))
        );
        assert!(
            codegen_const_issue(&ConstValue::FloatBits { bits: 0, width: 32 })
                .is_some_and(|detail| detail.contains("no executable TrustIr bridge lowering"))
        );
        assert!(codegen_const_issue(&ConstValue::Uint(255, 8)).is_none());
        assert!(
            codegen_const_issue(&ConstValue::CallableItem {
                def_path: "fixture::callback".to_string(),
                kind: CallableKind::FnDef,
                def_path_hash: CallableDefPathHash::new(1, 2),
            })
            .is_some()
        );
    }

    #[test]
    fn codegen_extraction_separates_verifier_abstractions_and_fails_closed() {
        let fixture = extract_codegen_fidelity_fixture();

        // Proof-authority quarantine: production verification extraction must leave
        // Builder::spawn's authenticated callee identity untouched. A forgeable
        // `::<__trust_spawn_namesafe>` suffix must never be emitted, even for the
        // literal, nul-free name shape the retired experimental analysis recognized.
        let spawn = fixture
            .verifier
            .get("spawn_with_literal_name")
            .expect("spawn_with_literal_name should be collected");
        let spawn_targets = extracted_call_targets(spawn);
        assert!(
            spawn_targets.iter().any(|callee| callee.contains("Builder::spawn")),
            "fixture must retain a Builder::spawn call, got {spawn_targets:?}"
        );
        assert!(
            spawn_targets.iter().all(|callee| !callee.contains("__trust_spawn_namesafe")),
            "production extraction must never stamp spawn proof authority: {spawn_targets:?}"
        );

        // The companion value-provenance experiment is retired too: even an Error
        // produced directly by from_raw_os_error keeps its real destruction operation.
        // Depending on the exact std/compiler revision, optimized MIR represents this
        // as either a Drop terminator or the still-authenticated core::mem::drop call.
        // The downstream bridge may fail closed on either shape, but extraction must
        // not turn it into an unauthenticated Goto discharge.
        let drop_os_error =
            fixture.verifier.get("drop_os_error").expect("drop_os_error should be collected");
        let is_io_error_place = |place: &Place| {
            matches!(
                drop_os_error.body.locals.get(place.local).map(|local| &local.ty),
                Some(Ty::Adt { name, .. }) if name.contains("::io::") && name.ends_with("::Error")
            )
        };
        assert!(
            drop_os_error.body.blocks.iter().any(|block| {
                match &block.terminator {
                    Terminator::Drop { place, .. } => is_io_error_place(place),
                    Terminator::Call { func, args, .. }
                        if func.starts_with("core::mem::drop::<")
                            && func.contains("::io::error::Error") =>
                    {
                        matches!(
                            args.as_slice(),
                            [Operand::Move(place) | Operand::Copy(place)] if is_io_error_place(place)
                        )
                    }
                    _ => false,
                }
            }),
            "production extraction must preserve the std::io::Error destruction operation: {drop_os_error:?}"
        );

        fixture
            .codegen
            .get("identity")
            .expect("identity should be collected")
            .as_ref()
            .expect("scalar identity should have a codegen-faithful extraction");

        let verifier_exit = fixture
            .verifier
            .get("exit_now")
            .expect("exit_now should be collected for verification");
        // Trust (never-typed divergence, 2026-09-18): the PROPERTY this row exists to
        // protect is that `process::exit` is not ERASED into a path-ending `Return` —
        // the `is_total_noreturn_call` hazard, where a forgeable display path would
        // excuse a user `my::process::exit -> !`'s body and effects. It is NOT "the
        // terminator is the `Opaque` sentinel". `process::exit` is typed `-> !`, so
        // extraction now keeps it as the faithful no-normal-successor `Call`
        // (`convert::direct_callee_returns_never`), which retains strictly MORE than
        // the sentinel did — the compiler-authenticated `callee_identity`, the
        // arguments, and the destination, none of which a `kind: String` carried —
        // while still inventing no continuation. Both halves are asserted below, so
        // the guard is now stated as the property rather than as one mechanism.
        assert!(
            verifier_exit.body.blocks.iter().any(|block| {
                matches!(
                    &block.terminator,
                    Terminator::Call { func, target: None, callee_identity: Some(_), .. }
                        if func.contains("process::exit")
                )
            }),
            "process::exit must be RETAINED as a diverging call with its authenticated \
             callee identity: {verifier_exit:?}"
        );
        assert!(
            !verifier_exit.body.blocks.iter().any(|block| {
                matches!(&block.terminator, Terminator::Return | Terminator::Goto(_))
            }),
            "process::exit must never gain a normal continuation — a `Return` or `Goto` \
             here is the path-ending rewrite `is_total_noreturn_call` stays disabled to \
             prevent: {verifier_exit:?}"
        );

        // The CODEGEN lane's property is unchanged and now stated on the shape rather
        // than on the `Opaque` sentinel: a call with no normal-return target has no
        // executable TrustIr representation, so extraction refuses it. The refusal is a
        // `SemanticAbstraction` — the same classification the disabled
        // `is_total_noreturn_call` guard above would have produced, and the same one
        // every other diverging call now gets, rather than one keyed on a forgeable
        // display path.
        let exit = fixture.codegen.get("exit_now").expect("exit_now should be collected");
        assert!(
            matches!(exit, Err(CodegenExtractionError::SemanticAbstraction { detail, .. })
                if detail.contains("diverges")
                    && detail.contains("process::exit")
                    && detail.contains("no no-return call terminator")),
            "process::exit must fail codegen closed as a diverging call, never become a normal return: {exit:?}"
        );

        let unwind =
            fixture.codegen.get("calls_may_panic").expect("calls_may_panic should be collected");
        assert!(
            matches!(unwind, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("unwind") || detail.contains("Unwind")),
            "call cleanup/continue semantics must fail closed: {unwind:?}"
        );

        let checked = fixture.codegen.get("checked_add").expect("checked_add should be collected");
        assert!(
            matches!(checked, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("Assert") || detail.contains("assert")),
            "assert panic payload/unwind semantics must fail closed: {checked:?}"
        );

        let opaque = fixture.codegen.get("opaque_bytes").expect("opaque_bytes should be collected");
        assert!(
            matches!(opaque, Err(CodegenExtractionError::UnsupportedMir { detail, .. })
                if detail.contains("constant") || detail.contains("symbolic")),
            "opaque constants must fail closed before codegen: {opaque:?}"
        );

        let verifier_derived = fixture
            .verifier
            .get("derived_clone_impl")
            .expect("derived Clone impl should be collected");
        assert!(
            verifier_derived.body.blocks.len() != 1
                || !verifier_derived.body.blocks[0].stmts.is_empty()
                || !matches!(verifier_derived.body.blocks[0].terminator, Terminator::Return),
            "verification mode must preserve the real derived body, never synthetic empty proof input"
        );
        let clone_caller = fixture
            .verifier
            .get("clone_derived")
            .expect("derived Clone caller should be collected");
        let clone_targets = extracted_call_targets(clone_caller);
        assert_eq!(
            clone_targets,
            vec![trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL.to_string()],
            "the compiler-authenticated total derived Clone uses the verifier abstraction",
        );
        let faithful_clone_caller = fixture
            .faithful_clone_caller
            .as_ref()
            .expect("faithful derived Clone caller should be collected");
        assert!(
            faithful_clone_caller.body.blocks.iter().any(|block| {
                matches!(
                    &block.terminator,
                    Terminator::Call { func, callee_identity: Some(_), .. }
                        if func.ends_with("::clone")
                            && func.contains("Clone")
                            && func.contains("Derived")
                )
            }),
            "faithful extraction must preserve the real derived Clone call and its compiler identity: {:?}",
            extracted_call_targets(faithful_clone_caller),
        );
        let raw_codegen_derived = fixture
            .raw_codegen
            .get("derived_clone_impl")
            .expect("raw codegen-purpose derived body should be collected");
        assert!(
            raw_codegen_derived.body.blocks.len() != 1
                || !raw_codegen_derived.body.blocks[0].stmts.is_empty()
                || !matches!(raw_codegen_derived.body.blocks[0].terminator, Terminator::Return),
            "codegen purpose must retain the real derived method body"
        );
        assert!(
            fixture
                .codegen
                .get("derived_clone_impl")
                .expect("derived Clone codegen result should be collected")
                .is_err(),
            "layout-erased derived code must fail closed, never emit havoc/trivial return"
        );
    }

    #[test]
    fn trust_annotation_snippets_parse_conservatively() {
        let boundary = trust_annotations_from_attr_snippet("#[trust(boundary)]");
        assert_eq!(boundary.len(), 1);
        assert_eq!(boundary[0].0, TrustAnnotationKind::Boundary);
        assert!(boundary[0].1.is_empty());

        let model = trust_annotations_from_attr_snippet("#[trust(model)]");
        assert_eq!(model.len(), 1);
        assert_eq!(model[0].0, TrustAnnotationKind::Model);
        assert!(model[0].1.is_empty());

        let assume = trust_annotations_from_attr_snippet(
            "#[trust(assume = \"calls an authenticated gateway\")]",
        );
        assert_eq!(assume.len(), 1);
        assert_eq!(assume[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(assume[0].1, "calls an authenticated gateway");

        let nested = trust_annotations_from_attr_snippet(
            "#[trust(boundary, assume(\"exactly once\"), model)]",
        );
        assert_eq!(nested.len(), 3);
        assert_eq!(nested[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(nested[1].0, TrustAnnotationKind::Assumption);
        assert_eq!(nested[1].1, "exactly once");
        assert_eq!(nested[2].0, TrustAnnotationKind::Model);

        let direct = trust_annotations_from_attr_snippet(
            "#[trust_assume = \"state transitions are explicit\"]",
        );
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(direct[0].1, "state transitions are explicit");
    }

    #[test]
    fn trust_annotation_snippets_ignore_unrelated_attrs() {
        assert!(trust_annotations_from_attr_snippet("#[doc = \"hello\"]").is_empty());
        assert!(trust_annotations_from_attr_snippet("#[trust(other)]").is_empty());
    }

    #[test]
    fn extracted_call_targets_use_semantic_paths_not_codegen_symbols() {
        let fixture = extract_call_target_fixture();

        let helper = fixture.functions.get("helper").expect("helper should be extracted");
        let caller = fixture.functions.get("caller").expect("caller should be extracted");
        let exit_wrapper =
            fixture.functions.get("exit_wrapper").expect("exit_wrapper should be extracted");

        assert_eq!(helper.name, "helper");
        assert!(
            helper.def_path.ends_with("::helper"),
            "expected semantic def_path for helper, got `{}`",
            helper.def_path
        );

        let caller_targets = extracted_call_targets(caller);
        assert_eq!(caller_targets, vec![helper.def_path.clone()]);
        assert_ne!(caller_targets[0], helper.name);

        let caller_symbols = fixture
            .direct_call_symbols
            .get("caller")
            .expect("caller direct-call symbols should be captured");
        assert_eq!(caller_symbols.len(), 1);
        assert_ne!(caller_targets[0], caller_symbols[0]);

        let exit_targets = extracted_call_targets(exit_wrapper);
        assert_eq!(exit_targets, vec![helper.def_path.clone()]);

        let exit_symbols = fixture
            .direct_call_symbols
            .get("exit_wrapper")
            .expect("exit_wrapper direct-call symbols should be captured");
        assert_eq!(exit_symbols.len(), 1);
        assert_ne!(exit_targets[0], exit_symbols[0]);
    }

    #[test]
    fn semantic_def_paths_are_crate_qualified_and_injective() {
        let fixture = extract_call_target_fixture();
        let crate_name = "trust_mir_extract_call_target_fixture";
        let root_item = format!("{crate_name}::collision");
        let same_named_module_item = format!("{crate_name}::{crate_name}::collision");

        assert_eq!(fixture.crate_def_path, crate_name);
        assert!(
            fixture.canonical_def_paths.contains(&root_item),
            "{:?}",
            fixture.canonical_def_paths
        );
        assert!(
            fixture.canonical_def_paths.contains(&same_named_module_item),
            "{:?}",
            fixture.canonical_def_paths
        );
        assert_ne!(root_item, same_named_module_item);
    }

    #[test]
    fn generic_call_targets_carry_exact_monomorphization_identity() {
        let fixture = extract_call_target_fixture();
        let caller = fixture
            .functions
            .get("mixed_generic_calls")
            .expect("mixed generic caller should be extracted");
        let targets = extracted_call_targets(caller);
        assert_eq!(targets.len(), 2, "{targets:?}");
        assert_ne!(targets[0], targets[1]);
        assert!(targets.iter().any(|target| target.contains("identity::<bool>")), "{targets:?}");
        assert!(targets.iter().any(|target| target.contains("identity::<i32>")), "{targets:?}");
    }

    #[test]
    fn function_item_call_operands_lower_to_fndef_types() {
        let fixture = extract_call_target_fixture();
        let caller = fixture.functions.get("caller").expect("caller should be extracted");
        let helper = fixture.functions.get("helper").expect("helper should be extracted");
        let call_types = fixture
            .direct_call_func_types
            .get("caller")
            .expect("caller direct-call function types should be captured");

        assert_eq!(call_types.len(), 1);
        let Ty::FnDef { name, sig } = &call_types[0] else {
            panic!("expected direct-call operand to lower as FnDef, got {:?}", call_types[0]);
        };
        assert_eq!(name, &helper.def_path);
        assert!(sig.params.is_empty(), "helper takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
        assert!(
            caller.body.locals.iter().all(|local| !matches!(local.ty, Ty::Unsupported { .. })),
            "callable type lowering should not inject Unsupported locals in caller: {:?}",
            caller.body.locals
        );
    }

    #[test]
    fn function_pointer_return_type_lowers_to_fnptr_signature() {
        let fixture = extract_call_target_fixture();
        let function =
            fixture.functions.get("helper_fn_ptr").expect("helper_fn_ptr should be extracted");

        let Ty::FnPtr { sig } = &function.body.return_ty else {
            panic!(
                "expected helper_fn_ptr return type to lower as FnPtr, got {:?}",
                function.body.return_ty
            );
        };
        assert!(sig.params.is_empty(), "helper function pointer takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
    }

    #[test]
    fn dyn_trait_references_lower_to_dynamic_pointees() {
        let fixture = extract_call_target_fixture();
        let function =
            fixture.functions.get("dyn_debug_ref").expect("dyn_debug_ref should be extracted");

        let Ty::Ref { inner: ret_inner, .. } = &function.body.return_ty else {
            panic!(
                "expected dyn_debug_ref return type to be a reference, got {:?}",
                function.body.return_ty
            );
        };
        let Ty::Dynamic { trait_name, .. } = ret_inner.as_ref() else {
            panic!("expected dyn_debug_ref return pointee to be Dynamic, got {ret_inner:?}");
        };
        assert_eq!(trait_name, "trust_mir_extract_call_target_fixture::LocalDebug");

        let arg = function
            .body
            .locals
            .iter()
            .find(|local| local.index == 1)
            .expect("dyn_debug_ref argument local should be present");
        let Ty::Ref { inner: arg_inner, .. } = &arg.ty else {
            panic!("expected dyn_debug_ref argument to be a reference, got {:?}", arg.ty);
        };
        assert!(matches!(arg_inner.as_ref(), Ty::Dynamic { .. }));
    }

    // Tests for parse_contract_specs

    #[test]
    fn parse_contract_specs_extracts_requires_as_preconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 1);
        assert!(post.is_empty());
        assert_eq!(
            pre[0],
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        // "result" maps to "_0" in the spec parser
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_extracts_closure_ensures_as_postconditions() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "|ret: &i32| *ret >= 0".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1);
        assert_eq!(
            post[0],
            Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    /// Closure-contract decompilation for a STRUCT-FIELD-referencing ensures:
    /// `|ret: &i32| *ret == p.value` normalizes to `result == p.value` and parses
    /// (general field projection) to `Eq(_0, Var("p.value"))`. Combined with the
    /// reflection/inhabitation field-projection grounding, this lets a real
    /// struct-accessor closure contract become a kernel-proven dependent type.
    #[test]
    fn parse_contract_specs_extracts_field_referencing_closure_ensures() {
        let contracts = vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "|ret: &i32| *ret == p.value".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert_eq!(post.len(), 1, "field-referencing closure ensures must no longer be dropped");
        assert_eq!(
            post[0],
            Formula::Eq(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Var("p.value".to_string(), Sort::Int)),
            )
        );
    }

    #[test]
    fn parse_contract_specs_handles_multiple_contracts() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "n < 100".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 2);
        assert_eq!(post.len(), 1);
    }

    #[test]
    fn parse_contract_specs_consumes_unique_exact_typed_proposition() {
        let contract = Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == x"),
        };
        let typed = Formula::Eq(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        );
        let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![CompilerContractProposition {
                source_contract_index: 0,
                kind: contract.kind,
                body: contract.body.clone(),
                formula: typed.clone(),
                variable_domains: vec![
                    trust_types::CompilerContractVariableDomain {
                        name: "_0".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                    },
                    trust_types::CompilerContractVariableDomain {
                        name: "x".to_string(),
                        domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                    },
                ],
            }]);

        let (pre, post) = parse_contract_specs_with_typed(&[contract], Some(&compiler_contracts));
        assert!(pre.is_empty());
        assert_eq!(post, vec![typed]);
    }

    #[test]
    fn typed_compiler_predicate_conversion_rejects_prefix_or_structure_drift() {
        use rustc_middle::mir::trust_contract::{
            TrustContractPredicateKind, TrustContractProposition as Proposition,
            TrustContractPropositionDomain as Domain,
        };

        rustc_span::create_default_session_globals_then(|| {
            let exact = TrustContractPredicateKind::Typed {
                text: Symbol::intern("__trust_lowered_compiler_contract__:x == 0"),
                proposition: Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert_eq!(
                convert_trust_contract_predicate(0, TrustContractKind::Ensures, &exact),
                Ok((
                    "__trust_lowered_compiler_contract__:x == 0".to_string(),
                    Some((
                        Formula::Eq(
                            Box::new(Formula::Var("x".to_string(), Sort::Int)),
                            Box::new(Formula::Int(0)),
                        ),
                        vec![trust_types::CompilerContractVariableDomain {
                            name: "x".to_string(),
                            domain: trust_types::CompilerContractValueDomain::MachineInt {
                                width: 8,
                                signed: false,
                            },
                        }],
                    )),
                ))
            );

            let missing_prefix = TrustContractPredicateKind::Typed {
                text: Symbol::intern("x == 0"),
                proposition: Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert!(
                convert_trust_contract_predicate(0, TrustContractKind::Ensures, &missing_prefix,)
                    .is_err()
            );

            let structural_drift = TrustContractPredicateKind::Typed {
                text: Symbol::intern("__trust_lowered_compiler_contract__:x == 0"),
                proposition: Proposition::Le(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            };
            assert!(
                convert_trust_contract_predicate(0, TrustContractKind::Ensures, &structural_drift,)
                    .is_err()
            );

            let signed_measure = TrustContractPredicateKind::Typed {
                text: Symbol::intern("__trust_lowered_compiler_contract__:-i"),
                proposition: Proposition::Neg(Box::new(Proposition::Var {
                    name: Symbol::intern("i"),
                    domain: Domain::MachineInt { width: 16, signed: true },
                })),
            };
            assert_eq!(
                convert_trust_contract_predicate(1, TrustContractKind::Decreases, &signed_measure,),
                Ok((
                    "__trust_lowered_compiler_contract__:-i".to_string(),
                    Some((
                        Formula::Neg(Box::new(Formula::Var("i".to_string(), Sort::Int,))),
                        vec![trust_types::CompilerContractVariableDomain {
                            name: "i".to_string(),
                            domain: trust_types::CompilerContractValueDomain::MachineInt {
                                width: 16,
                                signed: true,
                            },
                        }],
                    )),
                )),
                "a signed negative decreases measure retains its numeric typed carrier",
            );
            assert!(
                convert_trust_contract_predicate(
                    1,
                    TrustContractKind::LoopInvariant,
                    &signed_measure,
                )
                .is_err(),
                "a numeric measure cannot bind to a Boolean invariant kind",
            );
        });
    }

    #[test]
    fn bool_literal_typed_row_uses_canonical_compiler_prefix() {
        use rustc_middle::mir::trust_contract::TrustContractPredicateKind;

        assert_eq!(
            convert_trust_contract_predicate(
                0,
                TrustContractKind::Ensures,
                &TrustContractPredicateKind::BoolLiteral { value: true },
            ),
            Ok((
                format!("{LOWERED_COMPILER_CONTRACT_PREFIX}true"),
                Some((Formula::Bool(true), Vec::new())),
            ))
        );
        assert!(
            convert_trust_contract_predicate(
                0,
                TrustContractKind::Decreases,
                &TrustContractPredicateKind::BoolLiteral { value: true },
            )
            .is_err(),
            "a Boolean literal is not an E5 numeric measure",
        );
    }

    #[test]
    fn direct_call_collection_length_uses_canonical_summary_symbol() {
        let slice =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
        let source = Formula::Gt(
            Box::new(Formula::Var("xs__len".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let canonical =
            canonicalize_entry_collection_lengths(source, &[("xs".to_string(), slice.clone())])
                .expect("an unambiguous slice accessor must canonicalize");
        assert_eq!(
            canonical,
            Formula::Gt(
                Box::new(Formula::Var("xs__slice_len".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );

        // A parameter named `xs_len` is an ORDINARY binding: it neither blocks
        // nor is captured by the `xs__len` accessor leaf's canonicalization.
        let coexisting = canonicalize_entry_collection_lengths(
            Formula::Gt(
                Box::new(Formula::Var("xs__len".to_string(), Sort::Int)),
                Box::new(Formula::Var("xs_len".to_string(), Sort::Int)),
            ),
            &[("xs".to_string(), slice.clone()), ("xs_len".to_string(), Ty::usize())],
        )
        .expect("an ordinary `xs_len` parameter must not block canonicalization");
        assert_eq!(
            coexisting,
            Formula::Gt(
                Box::new(Formula::Var("xs__slice_len".to_string(), Sort::Int)),
                Box::new(Formula::Var("xs_len".to_string(), Sort::Int)),
            )
        );

        // Defensive invariant on caller-constructed parameter lists: a
        // parameter literally spelled like the reserved accessor leaf still
        // fails closed instead of aliasing.
        let collision = canonicalize_entry_collection_lengths(
            Formula::Var("xs__len".to_string(), Sort::Int),
            &[("xs".to_string(), slice), ("xs__len".to_string(), Ty::usize())],
        )
        .expect_err("a reserved-spelling parameter must never alias the generated accessor leaf");
        assert!(collision.contains("collides"), "unexpected rejection: {collision}");
    }

    #[test]
    fn parse_contract_specs_rejects_duplicate_or_stale_typed_provenance() {
        let requires = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        };
        let exact = CompilerContractProposition {
            source_contract_index: 0,
            kind: requires.kind,
            body: requires.body.clone(),
            formula: Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            variable_domains: vec![trust_types::CompilerContractVariableDomain {
                name: "x".to_string(),
                domain: trust_types::CompilerContractValueDomain::MathematicalInt,
            }],
        };
        let mut stale = exact.clone();
        stale.body.push_str(" && true");
        let compiler_contracts = CompilerContractBundle::new(vec![requires.clone()])
            .with_typed_propositions(vec![exact, stale]);

        let (pre, post) = parse_contract_specs_with_typed(&[requires], Some(&compiler_contracts));
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_rejects_formula_drift_with_exact_provenance_fields() {
        let requires = Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        };
        let compiler_contracts = CompilerContractBundle::new(vec![requires.clone()])
            .with_typed_propositions(vec![CompilerContractProposition {
                source_contract_index: 0,
                kind: requires.kind,
                body: requires.body.clone(),
                formula: Formula::Le(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                variable_domains: vec![trust_types::CompilerContractVariableDomain {
                    name: "x".to_string(),
                    domain: trust_types::CompilerContractValueDomain::MathematicalInt,
                }],
            }]);

        let (pre, post) = parse_contract_specs_with_typed(&[requires], Some(&compiler_contracts));
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_fails_closed_on_unparseable_requires() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "???invalid".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_fails_closed_on_empty_requires() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    #[test]
    fn parse_contract_specs_ignores_invariant_and_decreases() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Invariant,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Decreases,
                span: SourceSpan::default(),
                body: "n".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    // Trust: #472 — Additional tests to increase test density

    // --- contract_body_from_attr_snippet tests ---

    #[test]
    fn test_contract_body_from_attr_snippet_parenthesized() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(x > 0)]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_with_quotes() {
        assert_eq!(
            contract_body_from_attr_snippet("#[ensures(\"result >= 0\")]"),
            "\"result >= 0\""
        );
    }

    #[test]
    fn test_contract_body_from_attr_snippet_eq_form() {
        assert_eq!(contract_body_from_attr_snippet("#[requires = \"x > 0\"]"), "x > 0");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_no_body_returns_empty() {
        assert_eq!(contract_body_from_attr_snippet("#[requires]"), "");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_raw_text() {
        // No #[...] wrapper
        assert_eq!(contract_body_from_attr_snippet("requires(a + b < c)"), "a + b < c");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_nested_parens() {
        assert_eq!(contract_body_from_attr_snippet("#[requires(f(x) > g(y))]"), "f(x) > g(y)");
    }

    #[test]
    fn test_contract_body_from_attr_snippet_whitespace_trimmed() {
        assert_eq!(contract_body_from_attr_snippet("  #[requires(  a > b  )]  "), "a > b");
    }

    /// CONTRACT-NS-1: `contract_kind_from_attr` hands the attribute's whole path to
    /// this rule. The `trust::` spellings are contracts; the same last segment under
    /// another tool, or alone, is not.
    #[test]
    fn test_contract_attr_path_is_read_whole() {
        use trust_types::trust_attr_namespace::contract_kind_of_attr_path as kind;
        assert_eq!(kind(&["trust", "requires"]), Some(ContractKind::Requires));
        assert_eq!(kind(&["trust", "ensures"]), Some(ContractKind::Ensures));
        assert_eq!(kind(&["trust", "trust_requires"]), Some(ContractKind::Requires));
        assert_eq!(kind(&["clippy", "requires"]), None);
        assert_eq!(kind(&["rustfmt", "ensures"]), None);
        assert_eq!(kind(&["requires"]), None);
    }

    /// CONTRACT-NS-1: the markers this crate mints are exactly the ones a scraped
    /// contract body is refused for, so the refusal cannot drift from the minting.
    #[test]
    fn test_minted_contract_markers_are_refused_in_scraped_text() {
        use trust_types::trust_attr_namespace::compiler_contract_marker_in;
        assert_eq!(
            compiler_contract_marker_in(&format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x < 100")),
            Some(LOWERED_COMPILER_CONTRACT_PREFIX)
        );
        assert_eq!(
            compiler_contract_marker_in(&format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}x")),
            Some(UNSUPPORTED_COMPILER_CONTRACT_PREFIX)
        );
        assert_eq!(compiler_contract_marker_in("x < 100"), None);
    }

    #[test]
    fn test_normalized_contract_spec_body_unquotes_string_literal() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Requires, "\"x > 0\""),
            Some("x > 0".to_string())
        );
    }

    #[test]
    fn test_normalized_contract_spec_body_maps_ensures_closure_to_result() {
        assert_eq!(
            normalized_contract_spec_body(ContractKind::Ensures, "move |ret: &i32| { *ret >= 0 }"),
            Some("result >= 0".to_string())
        );
    }

    // --- strip_string_literal tests ---

    #[test]
    fn test_strip_string_literal_removes_quotes() {
        assert_eq!(strip_string_literal("\"hello world\""), "hello world");
    }

    #[test]
    fn test_strip_string_literal_no_quotes_passthrough() {
        assert_eq!(strip_string_literal("no_quotes"), "no_quotes");
    }

    #[test]
    fn test_strip_string_literal_empty_quoted() {
        assert_eq!(strip_string_literal("\"\""), "");
    }

    #[test]
    fn test_strip_string_literal_trims_whitespace() {
        assert_eq!(strip_string_literal("  \"trimmed\"  "), "trimmed");
    }

    #[test]
    fn test_strip_string_literal_single_quote_no_strip() {
        // Only matching double quotes are stripped
        assert_eq!(strip_string_literal("\"unmatched"), "\"unmatched");
    }

    // --- trust_annotation_from_item tests ---

    #[test]
    fn test_trust_annotation_from_item_boundary() {
        let result = trust_annotation_from_item("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_trust_boundary() {
        let result = trust_annotation_from_item("trust_boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotation_from_item_model() {
        let result = trust_annotation_from_item("model");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Model);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_retired_trust_model_annotation_is_not_accepted() {
        let result = trust_annotation_from_item("trust_model");
        assert!(result.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_assume_empty() {
        let result = trust_annotation_from_item("assume");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert!(result[0].1.is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_parens() {
        let result = trust_annotation_from_item("assume(\"safe by design\")");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "safe by design");
    }

    #[test]
    fn test_trust_annotation_from_item_assume_with_eq() {
        let result = trust_annotation_from_item("assume = \"always valid\"");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "always valid");
    }

    #[test]
    fn test_trust_annotation_from_item_empty_returns_empty() {
        assert!(trust_annotation_from_item("").is_empty());
    }

    #[test]
    fn test_trust_annotation_from_item_unknown_returns_empty() {
        assert!(trust_annotation_from_item("whatever").is_empty());
        assert!(trust_annotation_from_item("debug").is_empty());
        assert!(trust_annotation_from_item("inline").is_empty());
    }

    // --- contract_panic (T9) tests ---

    #[test]
    fn test_contract_panic_item_well_formed_extracts_payload() {
        for item in [
            "contract_panic(message_contains = \"capacity is\")",
            "trust_contract_panic(message_contains = \"capacity is\")",
            "trust::contract_panic(message_contains = \"capacity is\")",
            "contract_panic( message_contains=\"capacity is\" )",
        ] {
            let result = trust_annotation_from_item(item);
            assert_eq!(result.len(), 1, "item `{item}` should extract");
            assert_eq!(result[0].0, TrustAnnotationKind::ContractPanic);
            assert_eq!(result[0].1, "capacity is");
        }
    }

    #[test]
    fn test_contract_panic_nested_in_trust_list() {
        let anns = trust_annotations_from_attr_snippet(
            "#[trust(boundary, contract_panic(message_contains = \"lock poisoned, or\"))]",
        );
        assert_eq!(anns.len(), 2);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(anns[1].0, TrustAnnotationKind::ContractPanic);
        // The depth/string-aware splitter must keep a comma INSIDE the payload.
        assert_eq!(anns[1].1, "lock poisoned, or");
    }

    #[test]
    fn test_contract_panic_tool_attr_snippet_form() {
        let anns = trust_annotations_from_attr_snippet(
            "#[trust::contract_panic(message_contains = \"ArrayVec overflow\")]",
        );
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::ContractPanic);
        assert_eq!(anns[0].1, "ArrayVec overflow");
    }

    #[test]
    fn test_contract_panic_malformed_payload_is_error_not_silent_drop() {
        // Every malformed spelling must (a) extract NOTHING and (b) produce an
        // extraction error via `contract_panic_extraction_errors` — the silent
        // unknown-item drop is the anti-pattern for a recognized-but-broken
        // contract annotation.
        for snippet in [
            "#[trust(contract_panic)]",                            // no payload
            "#[trust(contract_panic())]",                          // empty parens
            "#[trust(contract_panic(message_contains))]",          // no value
            "#[trust(contract_panic(message_contains = ))]",       // no literal
            "#[trust(contract_panic(message_contains = \"\"))]",   // empty payload
            "#[trust(contract_panic(message_contains = \"  \"))]", // blank payload
            "#[trust(contract_panic(message_contains = bare))]",   // unquoted
            "#[trust(contract_panic(substring = \"x\"))]",         // wrong key
            "#[trust::contract_panic]",                            // tool form, no payload
        ] {
            assert!(
                trust_annotations_from_attr_snippet(snippet).is_empty(),
                "malformed `{snippet}` must not extract an annotation"
            );
            assert_eq!(
                contract_panic_extraction_errors(snippet).len(),
                1,
                "malformed `{snippet}` must produce exactly one extraction error"
            );
        }
    }

    #[test]
    fn test_contract_panic_well_formed_produces_no_errors() {
        for snippet in [
            "#[trust(contract_panic(message_contains = \"capacity is\"))]",
            "#[trust::contract_panic(message_contains = \"capacity is\")]",
            "#[trust(boundary)]",
            "#[doc = \"hello\"]",
            "#[trust(other)]", // unknown items stay silently dropped, not errors
        ] {
            assert!(
                contract_panic_extraction_errors(snippet).is_empty(),
                "`{snippet}` must not produce contract_panic errors"
            );
        }
    }

    #[test]
    fn test_contract_panic_prefix_collision_is_not_recognized() {
        // An identifier that merely SHARES the prefix is not a contract_panic
        // item: it must neither extract nor error (ordinary unknown-item drop).
        assert!(trust_annotation_from_item("contract_panicky").is_empty());
        assert!(contract_panic_extraction_errors("#[trust(contract_panicky)]").is_empty());
    }

    // --- trust_assumption_body tests ---

    #[test]
    fn test_trust_assumption_body_bare_assume() {
        assert_eq!(trust_assumption_body("assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume() {
        assert_eq!(trust_assumption_body("trust_assume"), Some(String::new()));
    }

    #[test]
    fn test_trust_assumption_body_paren_form() {
        assert_eq!(trust_assumption_body("assume(\"reason\")"), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_eq_form() {
        assert_eq!(trust_assumption_body("assume = \"reason\""), Some("reason".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_trust_assume_paren() {
        assert_eq!(trust_assumption_body("trust_assume(\"safe\")"), Some("safe".to_string()));
    }

    #[test]
    fn test_trust_assumption_body_not_assume_returns_none() {
        assert_eq!(trust_assumption_body("boundary"), None);
        assert_eq!(trust_assumption_body("model"), None);
        assert_eq!(trust_assumption_body("other"), None);
    }

    // --- split_trust_annotation_items tests ---

    #[test]
    fn test_split_trust_annotation_items_single() {
        let items = split_trust_annotation_items("boundary");
        assert_eq!(items, vec!["boundary"]);
    }

    #[test]
    fn test_split_trust_annotation_items_multiple() {
        let items = split_trust_annotation_items("boundary, model, assume");
        assert_eq!(items, vec!["boundary", "model", "assume"]);
    }

    #[test]
    fn test_split_trust_annotation_items_nested_parens() {
        let items = split_trust_annotation_items("assume(\"a, b\"), model");
        assert_eq!(items, vec!["assume(\"a, b\")", "model"]);
    }

    #[test]
    fn test_split_trust_annotation_items_empty() {
        let items = split_trust_annotation_items("");
        assert!(items.is_empty());
    }

    #[test]
    fn test_split_trust_annotation_items_escaped_strings() {
        let items = split_trust_annotation_items("assume(\"contains \\\"escaped\\\"\"), boundary");
        assert_eq!(items.len(), 2);
        assert_eq!(items[1], "boundary");
    }

    // --- trust_annotations_from_attr_body tests ---

    #[test]
    fn test_trust_annotations_from_attr_body_trust_wrapper() {
        let anns = trust_annotations_from_attr_body("trust(boundary)");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_direct_item() {
        let anns = trust_annotations_from_attr_body("boundary");
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn test_trust_annotations_from_attr_body_trust_multi() {
        let anns = trust_annotations_from_attr_body("trust(boundary, model)");
        assert_eq!(anns.len(), 2);
        assert_eq!(anns[0].0, TrustAnnotationKind::Boundary);
        assert_eq!(anns[1].0, TrustAnnotationKind::Model);
    }

    // --- parse_contract_specs edge cases ---

    #[test]
    fn test_parse_contract_specs_empty_contracts() {
        let (pre, post) = parse_contract_specs(&[]);
        assert!(pre.is_empty());
        assert!(post.is_empty());
    }

    #[test]
    fn test_parse_contract_specs_mixed_valid_invalid() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "???invalid".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result == 1".to_string(),
            },
        ];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre.len(), 2, "invalid requires must remain an explicit caller obligation");
        assert!(pre.iter().any(|formula| formula == &Formula::Bool(false)));
        assert_eq!(post.len(), 1, "valid ensures should be parsed");
    }

    #[test]
    fn test_parse_contract_specs_only_whitespace_body() {
        let contracts = vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "\t\n  ".to_string(),
        }];
        let (pre, post) = parse_contract_specs(&contracts);
        assert_eq!(pre, vec![Formula::Bool(false)]);
        assert!(post.is_empty());
    }

    // --- trust_annotations_from_attr_snippet edge cases ---

    #[test]
    fn test_trust_annotations_from_attr_snippet_empty() {
        assert!(trust_annotations_from_attr_snippet("").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_whitespace_only() {
        assert!(trust_annotations_from_attr_snippet("   ").is_empty());
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_trust_assume_eq_form() {
        let result =
            trust_annotations_from_attr_snippet("#[trust_assume = \"sound by construction\"]");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Assumption);
        assert_eq!(result[0].1, "sound by construction");
    }

    #[test]
    fn test_trust_annotations_from_attr_snippet_bare_boundary() {
        let result = trust_annotations_from_attr_snippet("boundary");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, TrustAnnotationKind::Boundary);
    }

    #[test]
    fn convert_trust_contract_bundle_maps_supported_requires_ensures_payloads() {
        let fixture = extract_contract_fixture();
        let converted = &fixture.conversion.supported.contracts;

        assert_eq!(converted.len(), 2);
        assert_eq!(converted[0].kind, ContractKind::Requires);
        assert_eq!(converted[0].body, "x > 0");
        assert_eq!(converted[0].span, SourceSpan::default());
        assert_eq!(converted[1].kind, ContractKind::Ensures);
        assert_eq!(converted[1].body, format!("{LOWERED_COMPILER_CONTRACT_PREFIX}true"));
    }

    #[test]
    fn convert_trust_contract_bundle_accepts_empty_bundle() {
        let fixture = extract_contract_fixture();
        assert!(fixture.conversion.empty.contracts.is_empty());
    }

    #[test]
    fn convert_trust_contract_bundle_maps_function_decreases() {
        rustc_span::create_default_session_globals_then(|| {
            let index = 7;
            assert_eq!(
                convert_trust_contract_kind(index, TrustContractKind::Decreases),
                Ok(ContractKind::Decreases)
            );
            assert_eq!(
                convert_trust_contract_subject(index, TrustContractSubject::Function),
                Ok(())
            );
            let (body, proposition) = convert_trust_contract_predicate(
                index,
                TrustContractKind::Decreases,
                &TrustContractPredicateKind::Opaque { text: sym::trust_test_contract_x_gt_zero },
            )
            .expect("function decreases payload should remain visible");
            assert_eq!(body, "x > 0");
            assert_eq!(proposition, None);
            assert_eq!(
                convert_trust_contract_kind(index, TrustContractKind::Invariant),
                Err(TrustContractBundleConversionError::UnsupportedContractKind {
                    index,
                    kind: "Invariant".to_string(),
                })
            );
        });
    }

    #[test]
    fn convert_trust_contract_bundle_preserves_unsupported_predicates_fail_closed() {
        let fixture = extract_contract_fixture();

        assert_eq!(fixture.conversion.unsupported.contracts.len(), 1);
        assert_eq!(fixture.conversion.unsupported.contracts[0].kind, ContractKind::Requires);
        assert_eq!(
            fixture.conversion.unsupported.contracts[0].body,
            format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}not_lowered")
        );
        assert_eq!(
            fixture.conversion.mir_local_error,
            Some(TrustContractBundleConversionError::MirLocalPredicate { index: 0, local: 1 })
        );
        assert_eq!(
            fixture.conversion.unsupported_kind_error,
            Some(TrustContractBundleConversionError::UnsupportedContractKind {
                index: 0,
                kind: "Invariant".to_string(),
            })
        );
        assert_eq!(
            fixture.conversion.nonconvertible_error,
            Some(TrustContractBundleConversionError::NonConvertibleNonEmptyBundle {
                summary_total: 1,
            })
        );
    }

    #[test]
    fn loop_contract_bundles_count_metadata_and_convert_into_parallel_lane() {
        let fixture = extract_contract_fixture();

        assert!(!fixture.conversion.loop_only_is_empty);
        assert_eq!(fixture.conversion.loop_only_len, 2);
        assert_eq!(fixture.conversion.loop_only_iter_count, 2);

        // E4/E5: authored loop clauses convert into the parallel
        // `loop_contracts` lane — never dropped, never silently merged into
        // the dense function-contract index. Unsupported predicate payloads
        // keep their explicit fail-closed marker so the vcgen pairing lane
        // (`bind_compiler_loop_contracts`) rejects them loudly.
        assert!(fixture.conversion.loop_only.contracts.is_empty());
        assert_eq!(fixture.conversion.loop_only.loop_contracts.len(), 2);
        assert_eq!(
            fixture.conversion.loop_only.loop_contracts[0].kind,
            trust_types::LoopContractKind::Invariant
        );
        assert_eq!(
            fixture.conversion.loop_only.loop_contracts[1].kind,
            trust_types::LoopContractKind::Decreases
        );
        assert!(
            fixture.conversion.loop_only.loop_contracts[0]
                .body
                .starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX)
        );

        assert_eq!(fixture.conversion.mixed_loop.contracts.len(), 2);
        assert_eq!(fixture.conversion.mixed_loop.loop_contracts.len(), 1);
        assert_eq!(
            fixture.conversion.mixed_loop.loop_contracts[0].kind,
            trust_types::LoopContractKind::Invariant
        );

        assert_eq!(
            fixture.conversion.mixed_loop_caller_fallback,
            (vec![Formula::Bool(false)], Vec::new()),
            "a conversion failure must still preserve a declared requires as an impossible caller obligation and withhold ensures",
        );
        assert_eq!(fixture.conversion.mixed_loop.contracts.len(), 2);
        assert_eq!(fixture.conversion.mixed_loop.loop_contracts.len(), 1);

        let typed_loop = &fixture.conversion.typed_loop;
        assert_eq!(typed_loop.contracts.len(), 2);
        assert_eq!(typed_loop.loop_contracts.len(), 1);
        assert_eq!(
            typed_loop.typed_propositions.last(),
            Some(&CompilerContractProposition {
                source_contract_index: 2,
                kind: ContractKind::LoopInvariant,
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}true"),
                formula: Formula::Bool(true),
                variable_domains: vec![],
            }),
            "loop propositions occupy the global dense+loop index and retain their exact source body",
        );
    }

    fn portable_loop_spec(
        kind: LoopContractKind,
        source_loop_id: u32,
        source_hir_local_id: u32,
        mir_header: Option<usize>,
    ) -> LoopContractSpec {
        LoopContractSpec {
            kind,
            source_loop_id,
            source_hir_local_id: Some(source_hir_local_id),
            mir_header,
            loop_head: SourceSpan::default(),
            header_span: SourceSpan::default(),
            span: SourceSpan::default(),
            body: "true".to_string(),
        }
    }

    #[test]
    fn loop_header_provenance_rejects_conflicting_endpoint_identities() {
        let mut bundle = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
            portable_loop_spec(LoopContractKind::Invariant, 0, 10, Some(90)),
            portable_loop_spec(LoopContractKind::Invariant, 1, 20, Some(91)),
        ]);
        let failures = stamp_loop_header_provenance_from_backedges(
            &[StampedNaturalBackedge {
                header: 3,
                header_hir_local_id: Some(10),
                latch_hir_local_id: Some(20),
            }],
            0,
            &mut bundle,
        );

        assert_eq!(failures.iter().map(|(source, _)| *source).collect::<Vec<_>>(), [0, 1]);
        assert!(
            failures.iter().all(|(_, reason)| reason.contains("e45.loop-source.no-mir-header")),
            "conflicting endpoint stamps must mint no header authority: {failures:?}",
        );
        assert!(
            bundle.loop_contracts.iter().all(|spec| spec.mir_header.is_none()),
            "failed restamping must clear every stale header",
        );
    }

    #[test]
    fn loop_header_provenance_accepts_header_only_and_latch_only_stamps() {
        for (label, header_hir_local_id, latch_hir_local_id, duplicate_edge) in
            [("header-only", Some(10), None, true), ("latch-only", None, Some(10), false)]
        {
            let mut bundle = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
                portable_loop_spec(LoopContractKind::Invariant, 0, 10, None),
                portable_loop_spec(LoopContractKind::Decreases, 0, 10, None),
            ]);
            let backedge =
                StampedNaturalBackedge { header: 3, header_hir_local_id, latch_hir_local_id };
            let backedges = if duplicate_edge { vec![backedge, backedge] } else { vec![backedge] };
            let failures = stamp_loop_header_provenance_from_backedges(&backedges, 0, &mut bundle);

            assert!(failures.is_empty(), "{label} compiler stamp must bind: {failures:?}");
            assert!(
                bundle.loop_contracts.iter().all(|spec| spec.mir_header == Some(3)),
                "{label}: every clause in one source group must receive the same exact header",
            );
        }
    }

    #[test]
    fn loop_header_provenance_names_cross_crate_inlined_scopes_on_a_miss() {
        // The MIR inliner appends an inlined callee's `source_scopes` verbatim,
        // and a callee decoded from another crate's metadata carries
        // `ClearCrossCrate::Clear`. Backedges with such an endpoint are dropped
        // before candidacy; a resulting miss must SAY that rather than claim the
        // authored loop had no natural MIR header at all.
        let mut bundle =
            CompilerContractBundle::new(vec![]).with_loop_contracts(vec![portable_loop_spec(
                LoopContractKind::Invariant,
                0,
                10,
                Some(90),
            )]);
        let failures = stamp_loop_header_provenance_from_backedges(&[], 2, &mut bundle);

        assert_eq!(failures.len(), 1);
        assert!(
            failures[0].1.contains("e45.loop-source.cross-crate-inlined-scope"),
            "a miss caused by cleared cross-crate scope data must name that cause: {failures:?}",
        );
        assert!(
            failures[0].1.contains("2 dominator-proved backedge(s)"),
            "the refusal must carry the dropped-backedge count: {failures:?}",
        );
        assert!(
            bundle.loop_contracts.iter().all(|spec| spec.mir_header.is_none()),
            "an unreadable mapping must clear every stale header, never mint one",
        );
    }

    #[test]
    fn cross_crate_opaque_backedges_never_grant_or_block_a_readable_binding() {
        // The count is reporting only: a readable backedge still binds exactly
        // as before, and the opaque ones contribute no candidate of their own.
        let mut bundle =
            CompilerContractBundle::new(vec![]).with_loop_contracts(vec![portable_loop_spec(
                LoopContractKind::Invariant,
                0,
                10,
                None,
            )]);
        let failures = stamp_loop_header_provenance_from_backedges(
            &[StampedNaturalBackedge {
                header: 3,
                header_hir_local_id: Some(10),
                latch_hir_local_id: Some(10),
            }],
            5,
            &mut bundle,
        );

        assert!(failures.is_empty(), "a readable backedge must still bind: {failures:?}");
        assert!(bundle.loop_contracts.iter().all(|spec| spec.mir_header == Some(3)));
    }

    /// One natural loop's backedge endpoints, as the scope data a body would
    /// carry for them: `Clear` is a scope appended by cross-crate MIR inlining,
    /// `Set(stamp)` a crate-local scope with (or without) a Trust loop stamp.
    type EndpointScope = mir::ClearCrossCrate<Option<u32>>;

    /// A real `mir::Body` with one natural loop per `(header, latch)` pair, laid
    /// out sequentially: `bb0 -> h0; h_i: switch(_1) { 0 => next, _ => l_i };
    /// l_i: goto h_i; exit: return`. Each loop contributes exactly ONE
    /// dominator-proved backedge `l_i -> h_i`, and each endpoint's terminator
    /// sits in its own source scope carrying the requested local data.
    fn loop_body_with_endpoint_scopes<'tcx>(
        loops: &[(EndpointScope, EndpointScope)],
    ) -> mir::Body<'tcx> {
        fn scope_data<'tcx>(
            parent: Option<mir::SourceScope>,
            data: EndpointScope,
        ) -> mir::SourceScopeData<'tcx> {
            mir::SourceScopeData {
                span: DUMMY_SP,
                parent_scope: parent,
                inlined: None,
                inlined_parent_scope: None,
                local_data: match data {
                    mir::ClearCrossCrate::Clear => mir::ClearCrossCrate::Clear,
                    mir::ClearCrossCrate::Set(stamp) => {
                        mir::ClearCrossCrate::Set(mir::SourceScopeLocalData {
                            lint_root: rustc_hir::CRATE_HIR_ID,
                            trust_loop_hir_local_id: stamp.map(rustc_hir::ItemLocalId::from_u32),
                        })
                    }
                },
            }
        }
        fn block<'tcx>(
            scope: mir::SourceScope,
            kind: mir::TerminatorKind<'tcx>,
        ) -> mir::BasicBlockData<'tcx> {
            mir::BasicBlockData::new(
                Some(mir::Terminator {
                    source_info: mir::SourceInfo { span: DUMMY_SP, scope },
                    kind,
                        }),
                false,
            )
        }

        let bb = mir::BasicBlock::from_usize;
        let exit = bb(1 + 2 * loops.len());
        let mut scopes = vec![scope_data(None, mir::ClearCrossCrate::Set(None))];
        let mut blocks =
            vec![block(mir::OUTERMOST_SOURCE_SCOPE, mir::TerminatorKind::Goto { target: bb(1), loop_hint_attrs: Default::default() })];
        for (i, &(header_scope, latch_scope)) in loops.iter().enumerate() {
            let (header, latch) = (bb(1 + 2 * i), bb(2 + 2 * i));
            let next = if i + 1 == loops.len() { exit } else { bb(3 + 2 * i) };
            let header_scope_id = mir::SourceScope::from_usize(scopes.len());
            scopes.push(scope_data(Some(mir::OUTERMOST_SOURCE_SCOPE), header_scope));
            let latch_scope_id = mir::SourceScope::from_usize(scopes.len());
            scopes.push(scope_data(Some(mir::OUTERMOST_SOURCE_SCOPE), latch_scope));
            blocks.push(block(
                header_scope_id,
                mir::TerminatorKind::SwitchInt {
                    discr: mir::Operand::Copy(mir::Place::from(mir::Local::from_u32(1))),
                    targets: mir::SwitchTargets::static_if(0, next, latch),
                },
            ));
            blocks.push(block(latch_scope_id, mir::TerminatorKind::Goto { target: header, loop_hint_attrs: Default::default() }));
        }
        blocks.push(block(mir::OUTERMOST_SOURCE_SCOPE, mir::TerminatorKind::Return));

        let mut body = mir::Body::new_cfg_only(blocks.into_iter().collect());
        for scope in scopes {
            body.source_scopes.push(scope);
        }
        body
    }

    #[test]
    fn body_level_stamping_counts_cleared_endpoints_and_refines_the_miss() {
        use mir::ClearCrossCrate::{Clear, Set};

        // Either endpoint cleared is a dropped backedge. The OTHER endpoint of
        // each carries the authored loop's stamp (HIR 10): flattening `Clear`
        // into "crate-local, unstamped" would let that stamp nominate the
        // header of foreign inlined MIR and BIND it — the exact failure
        // `ScopeLoopIdentity` exists to prevent.
        for (label, endpoints) in [
            ("cleared header, stamped latch", (Clear, Set(Some(10)))),
            ("stamped header, cleared latch", (Set(Some(10)), Clear)),
            ("both endpoints cleared", (Clear, Clear)),
        ] {
            let body = loop_body_with_endpoint_scopes(&[endpoints]);
            let mut bundle =
                CompilerContractBundle::new(vec![]).with_loop_contracts(vec![portable_loop_spec(
                    LoopContractKind::Invariant,
                    0,
                    10,
                    Some(90),
                )]);
            let failures = stamp_loop_header_provenance(&body, &mut bundle);

            assert_eq!(failures.len(), 1, "{label}: {failures:?}");
            assert_eq!(failures[0].0, 0, "{label}: the refusal names the source loop");
            assert!(
                failures[0]
                    .1
                    .starts_with("e45.loop-source.cross-crate-inlined-scope: HIR loop 10 "),
                "{label}: a cleared endpoint must refine the miss to the cross-crate code: \
                 {failures:?}",
            );
            assert!(
                failures[0].1.contains("; 1 dominator-proved backedge(s) in this body carry"),
                "{label}: exactly the one dropped backedge is counted: {failures:?}",
            );
            assert!(
                bundle.loop_contracts.iter().all(|spec| spec.mir_header.is_none()),
                "{label}: an unreadable mapping mints no header and keeps no stale one",
            );
        }
    }

    #[test]
    fn body_level_opaque_count_excludes_readable_backedges() {
        use mir::ClearCrossCrate::{Clear, Set};

        // Loops 0 and 1 each lose their backedge to a cleared endpoint; loop 2
        // is fully readable and stamped HIR 10, so its header (bb5) binds. The
        // refused group (HIR 30, no loop at all) must report the OPAQUE count,
        // 2 — not 3, which would count the readable edge it did inspect.
        let body = loop_body_with_endpoint_scopes(&[
            (Clear, Clear),
            (Set(Some(20)), Clear),
            (Set(Some(10)), Set(Some(10))),
        ]);
        let mut bundle = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
            portable_loop_spec(LoopContractKind::Invariant, 0, 10, None),
            portable_loop_spec(LoopContractKind::Invariant, 1, 30, Some(90)),
        ]);
        let failures = stamp_loop_header_provenance(&body, &mut bundle);

        assert_eq!(failures.len(), 1, "{failures:?}");
        assert_eq!(failures[0].0, 1);
        assert!(
            failures[0].1.starts_with("e45.loop-source.cross-crate-inlined-scope: HIR loop 30 "),
            "{failures:?}",
        );
        assert!(
            failures[0].1.contains("; 2 dominator-proved backedge(s) in this body carry"),
            "the count is the dropped backedges only: {failures:?}",
        );
        assert_eq!(bundle.loop_contracts[0].mir_header, Some(5), "the readable loop still binds");
        assert_eq!(bundle.loop_contracts[1].mir_header, None);
    }

    #[test]
    fn body_level_unstamped_local_scopes_are_not_reported_as_cross_crate() {
        use mir::ClearCrossCrate::Set;

        // The opposite direction of the refinement: a crate-local loop whose
        // scopes simply carry no stamp is an ordinary miss. Reporting it as a
        // cross-crate inlining artifact would misname the cause.
        let body = loop_body_with_endpoint_scopes(&[(Set(None), Set(None))]);
        let mut bundle =
            CompilerContractBundle::new(vec![]).with_loop_contracts(vec![portable_loop_spec(
                LoopContractKind::Invariant,
                0,
                10,
                Some(90),
            )]);
        let failures = stamp_loop_header_provenance(&body, &mut bundle);

        assert_eq!(failures.len(), 1, "{failures:?}");
        assert!(
            failures[0].1.starts_with("e45.loop-source.no-mir-header: HIR loop 10 matched 0 "),
            "{failures:?}",
        );
        assert!(bundle.loop_contracts.iter().all(|spec| spec.mir_header.is_none()));
    }

    #[test]
    fn loop_header_provenance_rejects_one_sided_identity_on_distinct_headers() {
        let mut bundle = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
            portable_loop_spec(LoopContractKind::Invariant, 0, 10, Some(90)),
            portable_loop_spec(LoopContractKind::Decreases, 0, 10, Some(90)),
        ]);
        let failures = stamp_loop_header_provenance_from_backedges(
            &[
                StampedNaturalBackedge {
                    header: 3,
                    header_hir_local_id: Some(10),
                    latch_hir_local_id: None,
                },
                // Model a stale outer stamp surviving on one endpoint of a
                // distinct nested natural loop. One source identity must not
                // select either header by order or span.
                StampedNaturalBackedge {
                    header: 7,
                    header_hir_local_id: None,
                    latch_hir_local_id: Some(10),
                },
            ],
            0,
            &mut bundle,
        );

        assert_eq!(failures.len(), 1);
        assert!(
            failures[0].1.contains("e45.loop-source.ambiguous-mir-header"),
            "one-sided cross-header identity reuse must fail closed: {failures:?}"
        );
        assert!(
            bundle.loop_contracts.iter().all(|spec| spec.mir_header.is_none()),
            "ambiguous one-sided provenance must clear every stale binding"
        );
    }

    #[test]
    fn loop_header_provenance_rejects_duplicate_hir_and_header_authority() {
        let mut duplicate_hir = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
            portable_loop_spec(LoopContractKind::Invariant, 0, 10, Some(80)),
            portable_loop_spec(LoopContractKind::Invariant, 1, 10, Some(81)),
        ]);
        let failures = stamp_loop_header_provenance_from_backedges(
            &[StampedNaturalBackedge {
                header: 3,
                header_hir_local_id: Some(10),
                latch_hir_local_id: Some(10),
            }],
            0,
            &mut duplicate_hir,
        );
        assert_eq!(failures.len(), 2);
        assert!(
            failures
                .iter()
                .all(|(_, reason)| reason.contains("e45.loop-source.non-injective-hir-id")),
            "one HIR loop cannot authenticate two source groups: {failures:?}",
        );
        assert!(duplicate_hir.loop_contracts.iter().all(|spec| spec.mir_header.is_none()));

        let mut duplicate_header = CompilerContractBundle::new(vec![]).with_loop_contracts(vec![
            portable_loop_spec(LoopContractKind::Invariant, 0, 10, Some(80)),
            portable_loop_spec(LoopContractKind::Invariant, 1, 20, Some(81)),
        ]);
        let failures = stamp_loop_header_provenance_from_backedges(
            &[
                StampedNaturalBackedge {
                    header: 3,
                    header_hir_local_id: Some(10),
                    latch_hir_local_id: Some(10),
                },
                StampedNaturalBackedge {
                    header: 3,
                    header_hir_local_id: Some(20),
                    latch_hir_local_id: Some(20),
                },
            ],
            0,
            &mut duplicate_header,
        );
        assert_eq!(failures.len(), 2);
        assert!(
            failures
                .iter()
                .all(|(_, reason)| { reason.contains("e45.loop-source.non-injective-mir-header") }),
            "one MIR header cannot merge two source-loop groups: {failures:?}",
        );
        assert!(duplicate_header.loop_contracts.iter().all(|spec| spec.mir_header.is_none()));
    }

    #[test]
    fn loop_header_provenance_clears_stale_header_when_no_binding_exists() {
        let mut bundle =
            CompilerContractBundle::new(vec![]).with_loop_contracts(vec![portable_loop_spec(
                LoopContractKind::Invariant,
                0,
                10,
                Some(99),
            )]);
        let failures = stamp_loop_header_provenance_from_backedges(&[], 0, &mut bundle);

        assert_eq!(failures.len(), 1);
        assert!(failures[0].1.contains("e45.loop-source.no-mir-header"));
        assert_eq!(bundle.loop_contracts[0].mir_header, None);
    }

    #[test]
    fn ordinary_rustc_config_stamps_nested_and_independent_loop_headers() {
        let fixture = extract_contract_fixture();

        for name in ["nested_loop_provenance", "independent_loop_provenance"] {
            let failures = fixture
                .loop_provenance_failures
                .get(name)
                .unwrap_or_else(|| panic!("{name}: loop provenance result must be recorded"));
            assert!(failures.is_empty(), "{name}: provenance failures: {failures:?}");

            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .unwrap_or_else(|| panic!("{name}: converted loop bundle must be recorded"));
            assert_eq!(bundle.loop_contracts.len(), 4, "{name}: two clauses per loop");
            assert_eq!(
                bundle.typed_propositions.len(),
                4,
                "{name}: real native loop clauses must cross the query as structural propositions",
            );
            assert!(
                bundle.typed_propositions.iter().all(|proposition| {
                    proposition.body.starts_with(LOWERED_COMPILER_CONTRACT_PREFIX)
                        && !proposition.variable_domains.is_empty()
                }),
                "{name}: each loop proposition must retain exact visible variable domains",
            );
            if name == "nested_loop_provenance" {
                for proposition in &bundle.typed_propositions {
                    let (variable, expected_domain) = if proposition.body.contains("inner") {
                        (
                            "inner",
                            CompilerContractValueDomain::MachineInt { width: 16, signed: true },
                        )
                    } else {
                        (
                            "outer",
                            CompilerContractValueDomain::MachineInt { width: 32, signed: false },
                        )
                    };
                    assert_eq!(
                        proposition.variable_domains,
                        vec![CompilerContractVariableDomain {
                            name: variable.to_string(),
                            domain: expected_domain,
                        }],
                        "{name}: nested loop domains must retain each visible binding's exact width and signedness",
                    );
                }
            }
            assert!(
                bundle.loop_contracts.iter().all(|spec| {
                    spec.source_hir_local_id.is_some() && spec.mir_header.is_some()
                }),
                "{name}: every clause must carry authenticated source and MIR identities",
            );

            let mut clauses_by_source = BTreeMap::<u32, Vec<&LoopContractSpec>>::new();
            for spec in &bundle.loop_contracts {
                clauses_by_source.entry(spec.source_loop_id).or_default().push(spec);
            }
            assert_eq!(clauses_by_source.len(), 2, "{name}: two distinct source loops");
            let headers = clauses_by_source
                .values()
                .map(|clauses| {
                    assert_eq!(clauses.len(), 2, "{name}: invariant/decreases pair");
                    assert_eq!(
                        clauses[0].source_hir_local_id, clauses[1].source_hir_local_id,
                        "{name}: a clause pair must agree on its source loop",
                    );
                    assert_eq!(
                        clauses[0].mir_header, clauses[1].mir_header,
                        "{name}: a clause pair must agree on its MIR header",
                    );
                    clauses[0].mir_header.expect("checked above")
                })
                .collect::<BTreeSet<_>>();
            assert_eq!(headers.len(), 2, "{name}: source loops must bind distinct headers");

            let mut function = fixture
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("{name}: function must be extracted"))
                .clone();
            let bind_failures =
                trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            assert!(bind_failures.is_empty(), "{name}: bind failures: {bind_failures:?}");
            let bound_loop_contracts = function
                .contracts
                .iter()
                .filter(|contract| {
                    matches!(contract.kind, ContractKind::LoopInvariant | ContractKind::Decreases)
                })
                .collect::<Vec<_>>();
            assert_eq!(bound_loop_contracts.len(), 4);
            for contract in bound_loop_contracts {
                assert!(
                    bundle.loop_contracts.iter().any(|spec| {
                        let kind = match spec.kind {
                            LoopContractKind::Invariant => ContractKind::LoopInvariant,
                            LoopContractKind::Decreases => ContractKind::Decreases,
                        };
                        contract.kind == kind
                            && contract.span == spec.span
                            && spec.mir_header.is_some_and(|header| {
                                contract.body == format!("bb{header}: {}", spec.body)
                            })
                    }),
                    "{name}: compiler loop clause must be canonically bound to its exact header",
                );
            }
        }
    }

    #[test]
    fn ordinary_rustc_config_binds_typed_literal_collection_projections() {
        let fixture = extract_contract_fixture();

        for name in ["immutable_slice_projection", "immutable_array_projection"] {
            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .unwrap_or_else(|| panic!("{name}: loop contract bundle must be recorded"));
            assert_eq!(bundle.loop_contracts.len(), 1, "{name}: one authored invariant");
            assert_eq!(bundle.typed_propositions.len(), 1, "{name}: one exact typed invariant");
            let proposition = &bundle.typed_propositions[0];
            assert_eq!(proposition.kind, ContractKind::LoopInvariant);
            assert!(
                proposition.body.starts_with(LOWERED_COMPILER_CONTRACT_PREFIX),
                "{name}: compiler schema prefix is part of source provenance",
            );
            assert_eq!(
                proposition
                    .variable_domains
                    .iter()
                    .find(|domain| domain.name == "xs[0]")
                    .map(|domain| domain.domain),
                Some(CompilerContractValueDomain::MachineInt { width: 32, signed: false }),
                "{name}: the projected element must retain its exact u32 domain",
            );

            let mut function = fixture
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("{name}: function must be extracted"))
                .clone();
            let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            assert!(failures.is_empty(), "{name}: exact typed binding failed: {failures:?}");
            let vcs = trust_vcgen::generate_vcs(&function);
            assert_eq!(
                vcs.iter()
                    .filter(|vc| matches!(
                        vc.kind,
                        VcKind::LoopInvariantInitiation { .. }
                            | VcKind::LoopInvariantConsecution { .. }
                    ))
                    .count(),
                2,
                "{name}: the production typed path must retain the E4 proof pair: {vcs:#?}",
            );
            assert!(
                !vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. }
                        if detail.contains("UserLoopContractUnsupported")
                            || detail.contains("e45.collection")
                )),
                "{name}: a stable immutable literal read must not hit a collection frontier: \
                 {vcs:#?}",
            );
        }
    }

    #[test]
    fn ordinary_rustc_config_denies_shadowed_collection_projection_authority() {
        let fixture = extract_contract_fixture();

        for name in ["shadowed_collection_index", "shadowed_collection_length"] {
            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .unwrap_or_else(|| panic!("{name}: loop contract bundle must be recorded"));
            assert_eq!(bundle.loop_contracts.len(), 1, "{name}: one authored invariant");
            // Trust: a typed proposition may now be RECORDED here, and recording is
            // NOT authority. MEASURED, because the first reading of this failure was
            // wrong: when this test began failing it looked like a false-accept, since
            // `bind_compiler_loop_contract_bundle` stopped reporting a rejection (1 ->
            // 0). It is not. Letting the two assertions below actually run shows the
            // clause still acquires NO authority -- no E4 initiation/consecution row is
            // minted, and the fail-closed row is still emitted. What moved is WHERE the
            // refusal is reported, not WHETHER.
            //
            // Why the binder stopped counting it: acceptance there is
            // `bundle.typed_proposition(..).is_some()` -- an EXISTENCE check. It asks
            // whether a typed proposition was recorded, never whether that proposition
            // can be grounded. Once the compiler began minting one for these clauses,
            // the existence check passed. Grounding is still refused downstream, by the
            // name-uniqueness guard in `read_only_collection_model_for_name`, which was
            // written for this exact fixture: two locals render as `xs`, so the lookup
            // is ambiguous and returns None rather than silently borrowing the outer
            // argument's array identity.
            //
            // So the old `failures.len() == 1` assertion pinned the LOCATION of a
            // refusal, not the safety property, and it is the assertions below that
            // carry the property. They are what this test is named for.
            //
            // The recorded proposition's only collection leaf is OPAQUE: its name is
            // the source text -- `Var("xs[0]")`, `Var("xs__len")` -- carrying no place
            // provenance whatsoever. Nothing about the leaf itself says WHICH `xs` it
            // names, which is the whole hazard these fixtures exist to trip: the inner
            // shadow makes each invariant FALSE (`[0u32; 4][0] == first` for an
            // arbitrary `first`; `[0u32; 2].len() == 4`) while the stable outer
            // argument would make it TRUE. A name-only consumer that resolved such a
            // leaf to the outer argument would prove a false invariant.
            //
            // If either assertion below moves, a wrong-place rebinding HAS acquired
            // authority and that is a false verify, not a stale expectation. Do not
            // relax them; find what started grounding the leaf.
            let recorded_without_provenance = bundle.typed_propositions.len();

            let mut function = fixture
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("{name}: function must be extracted"))
                .clone();
            let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            let binder_rejections = failures.len();
            let vcs = trust_vcgen::generate_vcs(&function);
            assert!(
                !vcs.iter().any(|vc| matches!(
                    vc.kind,
                    VcKind::LoopInvariantInitiation { .. }
                        | VcKind::LoopInvariantConsecution { .. }
                )),
                "{name}: AUTHORITY BREACH -- E4 rows minted for a wrong-place rebinding (binder_rejections={binder_rejections}, recorded={recorded_without_provenance}): {vcs:#?}",
            );
            assert!(
                vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. }
                        if detail.contains("no unique exact compiler-typed proposition")
                            || detail.contains("unsupported or ambiguous MIR value")
                )),
                "{name}: the denied clause must remain a visible fail-closed row (binder_rejections={binder_rejections}, recorded={recorded_without_provenance}): {vcs:#?}",
            );
        }
    }

    #[test]
    fn ordinary_rustc_config_denies_out_of_range_fixed_projection_authority() {
        let fixture = extract_contract_fixture();
        let name = "out_of_range_fixed_projection";
        let bundle = fixture
            .loop_contract_bundles
            .get(name)
            .expect("out-of-range loop contract bundle must be recorded");
        assert_eq!(bundle.loop_contracts.len(), 1);
        assert_eq!(bundle.loop_contracts[0].body, "xs[4] == xs[4]");
        assert!(
            bundle.typed_propositions.is_empty(),
            "the compiler query must not mint a projected identity at the `[T; N]` bound",
        );

        let mut function = fixture.functions.get(name).expect("function must be extracted").clone();
        let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
        assert_eq!(failures.len(), 1, "the strict binder must retain the opaque clause failure");
        let vcs = trust_vcgen::generate_vcs(&function);
        assert!(
            !vcs.iter().any(|vc| matches!(
                vc.kind,
                VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
            )),
            "VCgen must independently reject the out-of-range fixed-array leaf: {vcs:#?}",
        );
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { detail, .. }
                    if detail.contains("unsupported or ambiguous MIR value")
            )),
            "the out-of-range clause must remain a visible fail-closed row: {vcs:#?}",
        );
    }

    #[test]
    fn ordinary_rustc_config_extracts_exact_guarded_mutable_collection_stores() {
        let fixture = extract_contract_fixture();

        for name in ["mutable_slice_store", "mutable_fixed_store"] {
            let mut function = fixture
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("{name}: function must be extracted"))
                .clone();
            let xs_local = function
                .body
                .locals
                .iter()
                .find(|decl| decl.name.as_deref() == Some("xs"))
                .unwrap_or_else(|| panic!("{name}: source collection local must retain its name"))
                .index;
            assert!(matches!(
                &function.body.locals[xs_local].ty,
                Ty::Ref {
                    mutable: true,
                    inner,
                } if matches!(inner.as_ref(), Ty::Slice { elem } | Ty::Array { elem, .. }
                    if elem.as_ref() == &Ty::u32())
            ));

            let stores = function
                .body
                .blocks
                .iter()
                .flat_map(|block| {
                    block.stmts.iter().enumerate().filter_map(move |(statement, stmt)| {
                        matches!(stmt, Statement::Assign { place, .. }
                            if place.local == xs_local
                                && place.projections.first() == Some(&Projection::Deref))
                        .then_some((block.id, statement, stmt))
                    })
                })
                .collect::<Vec<_>>();
            let [(store_block, _, Statement::Assign { place: store_place, rvalue, .. })] =
                stores.as_slice()
            else {
                panic!("{name}: expected one exact projected store, got {stores:#?}");
            };
            assert!(matches!(
                store_place.projections.as_slice(),
                [Projection::Deref, Projection::Index(_)]
                    | [Projection::Deref, Projection::ConstantIndex { from_end: false, .. }]
            ));
            let Rvalue::Use(store_value) = rvalue else {
                panic!("{name}: store value must be a direct operand, got {rvalue:?}");
            };
            let store_value_is_u32 = match store_value {
                Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
                    function.body.locals.get(place.local).is_some_and(|decl| decl.ty == Ty::u32())
                }
                Operand::Constant(ConstValue::Uint(_, 32)) => true,
                _ => false,
            };
            assert!(
                store_value_is_u32,
                "{name}: extracted store value must retain the exact element type",
            );

            if name == "mutable_slice_store" {
                assert!(
                    function.body.blocks.iter().any(|block| {
                        matches!(
                            &block.terminator,
                            Terminator::Assert {
                                msg: AssertMessage::BoundsCheck,
                                target,
                                expected: true,
                                ..
                            } if target == store_block
                        )
                    }),
                    "{name}: the slice store must retain rustc's direct BoundsCheck edge",
                );
            }

            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .unwrap_or_else(|| panic!("{name}: native loop contract bundle must be recorded"));
            let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            assert!(failures.is_empty(), "{name}: loop binding failures: {failures:?}");
            let vcs = trust_vcgen::generate_vcs(&function);
            assert_eq!(
                vcs.iter()
                    .filter(|vc| matches!(
                        vc.kind,
                        VcKind::LoopInvariantInitiation { .. }
                            | VcKind::LoopInvariantConsecution { .. }
                    ))
                    .count(),
                2,
                "{name}: exact extracted mutable store must retain its E4 pair: {vcs:#?}",
            );
            assert!(
                !vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. } if detail.contains("e45.collection")
                        || detail.contains("e45.transition")
                )),
                "{name}: exact extracted mutable store must not hit an E4/E5 collection frontier: \
                 {vcs:#?}",
            );
        }
    }

    #[test]
    fn ordinary_rustc_config_extracts_retained_mutable_reborrow_and_terminal_escape() {
        // MIR-opt 0 intentionally retains rustc's storage markers and local
        // reborrow instead of letting copy propagation subsume it back into
        // the source argument. Verification must be sound at every supported
        // MIR optimization level, not only after the alias happens to vanish.
        let fixture = extract_contract_fixture_with_mir_opt_level(0);

        for name in ["mutable_slice_retained_reborrow", "mutable_slice_retained_return"] {
            let mut function = fixture
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("{name}: function must be extracted"))
                .clone();
            let xs_local = function
                .body
                .locals
                .iter()
                .find(|decl| decl.name.as_deref() == Some("xs"))
                .unwrap_or_else(|| panic!("{name}: source argument must retain its name"))
                .index;
            let alias_local = function
                .body
                .locals
                .iter()
                .find(|decl| decl.name.as_deref() == Some("retained"))
                .unwrap_or_else(|| panic!("{name}: retained reborrow must remain a MIR local"))
                .index;
            assert_eq!(function.body.locals[xs_local].ty, function.body.locals[alias_local].ty);

            let definitions = function
                .body
                .blocks
                .iter()
                .flat_map(|block| {
                    block.stmts.iter().enumerate().filter_map(move |(index, statement)| {
                        matches!(
                            statement,
                            Statement::Assign {
                                place,
                                rvalue: Rvalue::Ref { mutable: true, place: source },
                                ..
                            } if place.local == alias_local
                                && place.projections.is_empty()
                                && source.local == xs_local
                                && source.projections.as_slice() == [Projection::Deref]
                        )
                        .then_some((block.id, index))
                    })
                })
                .collect::<Vec<_>>();
            let [(definition_block, definition_index)] = definitions.as_slice() else {
                panic!("{name}: expected one exact retained reborrow, got {definitions:?}");
            };
            assert_eq!(*definition_block, BlockId(0), "{name}: reborrow must dominate the loop");
            assert!(
                function.body.blocks[0]
                    .stmts
                    .iter()
                    .take(*definition_index)
                    .any(|statement| matches!(statement, Statement::StorageLive(local) if *local == alias_local)),
                "{name}: the real rustc shape must exercise StorageLive before definition: \
                 {:#?}",
                function.body.blocks[0].stmts,
            );
            assert!(
                function.body.blocks.iter().any(|block| {
                    block.stmts.iter().any(|statement| {
                        matches!(statement, Statement::Assign { place, .. }
                            if place.local == alias_local
                                && matches!(place.projections.as_slice(),
                                    [Projection::Deref, Projection::Index(_)]
                                        | [Projection::Deref, Projection::ConstantIndex { from_end: false, .. }]))
                    })
                }),
                "{name}: the guarded store must execute through the retained alias",
            );

            if name == "mutable_slice_retained_return" {
                let exact_terminal_reborrow = function.body.blocks.iter().any(|block| {
                    matches!(block.terminator, Terminator::Return)
                        && block.stmts.iter().enumerate().any(|(index, first)| {
                            let Statement::Assign {
                                place: temporary,
                                rvalue: Rvalue::Ref { mutable: true, place: first_source },
                                ..
                            } = first
                            else {
                                return false;
                            };
                            let Some(Statement::StorageDead(dead_alias)) =
                                block.stmts.get(index + 1)
                            else {
                                return false;
                            };
                            let Some(Statement::Assign {
                                place: return_place,
                                rvalue: Rvalue::Ref { mutable: true, place: returned_temporary },
                                ..
                            }) = block.stmts.get(index + 2)
                            else {
                                return false;
                            };
                            let Some(Statement::StorageDead(dead_temporary)) =
                                block.stmts.get(index + 3)
                            else {
                                return false;
                            };
                            temporary.local > function.body.arg_count
                                && temporary.local != alias_local
                                && temporary.projections.is_empty()
                                && first_source.local == alias_local
                                && first_source.projections.as_slice() == [Projection::Deref]
                                && *dead_alias == alias_local
                                && return_place.local == 0
                                && return_place.projections.is_empty()
                                && returned_temporary.local == temporary.local
                                && returned_temporary.projections.as_slice() == [Projection::Deref]
                                && *dead_temporary == temporary.local
                                && function.body.locals.get(temporary.local).is_some_and(|decl| {
                                    decl.ty == function.body.return_ty
                                        && decl.ty == function.body.locals[alias_local].ty
                                })
                                && block.stmts.iter().skip(index + 4).all(|later| {
                                    matches!(
                                        later,
                                        Statement::StorageDead(_)
                                            | Statement::Coverage
                                            | Statement::ConstEvalCounter
                                            | Statement::Nop
                                    )
                                })
                        })
                });
                assert!(
                    exact_terminal_reborrow,
                    "{name}: escape authority is limited to rustc's exact terminal mutable-\
                     reborrow handoff; \
                     extracted body: {:#?}",
                    function.body,
                );
            }

            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .unwrap_or_else(|| panic!("{name}: native loop contract bundle must be recorded"));
            let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            assert!(failures.is_empty(), "{name}: loop binding failures: {failures:?}");
            let vcs = trust_vcgen::generate_vcs(&function);
            assert_eq!(
                vcs.iter()
                    .filter(|vc| matches!(
                        vc.kind,
                        VcKind::LoopInvariantInitiation { .. }
                            | VcKind::LoopInvariantConsecution { .. }
                    ))
                    .count(),
                2,
                "{name}: retained alias must keep the public E4 proof pair: {vcs:#?}; \
                 extracted body: {:#?}",
                function.body,
            );
            assert!(
                !vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. }
                        if detail.contains("e45.collection")
                            || detail.contains("e45.transition")
                )),
                "{name}: the exact compiler shape must not hit the alias frontier: {vcs:#?}",
            );
        }
    }

    #[test]
    fn ordinary_rustc_config_rejects_mutable_collection_call_alias_and_reseat_frontiers() {
        let fixture = extract_contract_fixture();
        for name in ["mutable_slice_call_escape", "mutable_slice_reseat"] {
            let mut function =
                fixture.functions.get(name).expect("function must be extracted").clone();
            let bundle = fixture
                .loop_contract_bundles
                .get(name)
                .expect("loop contract bundle must be recorded");
            let failures = trust_vcgen::bind_compiler_loop_contract_bundle(&mut function, bundle);
            assert!(failures.is_empty(), "{name}: loop binding failures: {failures:?}");
            let vcs = trust_vcgen::generate_vcs(&function);
            assert!(
                !vcs.iter().any(|vc| matches!(
                    vc.kind,
                    VcKind::LoopInvariantInitiation { .. }
                        | VcKind::LoopInvariantConsecution { .. }
                )),
                "{name}: a call/reborrow/reseat must not mint E4 rows: {vcs:#?}",
            );
            assert!(
                vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. }
                        if detail.contains("e45.collection.alias")
                            || detail.contains("e45.collection.call")
                            || detail.contains("e45.collection.mutation")
                            || detail.contains("e45.collection.unstable")
                )),
                "{name}: the excluded call/reborrow/reseat frontier must stay visible: {vcs:#?}",
            );
        }
    }

    #[test]
    fn ordinary_rustc_config_carries_typed_numeric_function_measure() {
        let fixture = extract_contract_fixture();
        let bundle = fixture
            .function_decreases_bundle
            .expect("native function decreases bundle must be recorded");
        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.contracts[0].kind, ContractKind::Decreases);
        assert_eq!(bundle.contracts[0].body, format!("{LOWERED_COMPILER_CONTRACT_PREFIX}n"),);
        assert_eq!(bundle.typed_propositions.len(), 1);
        let proposition = &bundle.typed_propositions[0];
        assert_eq!(proposition.kind, ContractKind::Decreases);
        assert_eq!(proposition.formula, Formula::Var("n".to_string(), Sort::Int));
        assert_eq!(
            proposition.variable_domains,
            vec![CompilerContractVariableDomain {
                name: "n".to_string(),
                domain: CompilerContractValueDomain::MachineInt { width: 32, signed: false },
            }],
        );
        assert_eq!(bundle.typed_proposition(0, &bundle.contracts[0]), Some(proposition));
    }

    #[test]
    fn current_rustc_contract_query_lowers_simple_comparison_predicate() {
        let fixture = extract_contract_fixture();
        let query_contracts =
            fixture.query_contracts.expect("reciprocal query contracts should convert");

        assert_eq!(query_contracts.contracts.len(), 1);
        assert_eq!(query_contracts.contracts[0].kind, ContractKind::Requires);
        assert_eq!(
            query_contracts.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(n) > (0)")
        );
        assert_eq!(
            normalized_contract_spec_body(
                query_contracts.contracts[0].kind,
                &query_contracts.contracts[0].body
            ),
            Some("(n) > (0)".to_string())
        );
    }

    #[test]
    fn compiler_contract_attrs_extract_into_pre_and_postconditions() {
        let fixture = extract_contract_fixture();
        let functions = &fixture.functions;

        let reciprocal = functions.get("reciprocal").expect("reciprocal should be extracted");
        assert_eq!(reciprocal.contracts.len(), 1);
        assert_eq!(
            reciprocal.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(n) > (0)")
        );
        assert_eq!(reciprocal.spec.requires, vec!["(n) > (0)".to_string()]);
        assert_eq!(
            reciprocal.preconditions,
            vec![
                Formula::Gt(
                    Box::new(Formula::Var("n".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::And(vec![
                    Formula::Ge(
                        Box::new(Formula::Var("n".to_string(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::Le(
                        Box::new(Formula::Var("n".to_string(), Sort::Int)),
                        Box::new(Formula::Int(u32::MAX.into())),
                    ),
                ]),
            ]
        );

        let abs_broken = functions.get("abs_broken").expect("abs_broken should be extracted");
        assert_eq!(abs_broken.contracts.len(), 1);
        assert_eq!(
            abs_broken.contracts[0].body,
            format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(result) >= (0)")
        );
        assert_eq!(abs_broken.spec.ensures, vec!["(result) >= (0)".to_string()]);
        assert_eq!(
            abs_broken.postconditions,
            vec![Formula::Ge(
                Box::new(Formula::Var("_0".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )]
        );

        let reciprocal_metadata =
            fixture.metadata.get("reciprocal").expect("reciprocal metadata should be extracted");
        assert!(!reciprocal_metadata.contract_extraction.source_scraping_used);
        // This fixture mirrors the production verifier path by converting and
        // passing rustc's typed `trust_contracts` query bundle. Deleting the
        // compat/debug scraper must preserve that stronger provenance label.
        assert_eq!(
            reciprocal_metadata.contract_extraction.source,
            ContractExtractionSource::CompilerContractBundle
        );
        // R2 deletion D-B: proof items come exclusively from the compiler-owned
        // bundle; no HIR-attribute proof import runs, so plain contract-bearing
        // functions carry no imported proof items.
        assert!(reciprocal_metadata.proof_items.is_empty());
    }

    #[test]
    fn empty_compiler_contract_bundle_does_not_invent_consumed_hir_contract_attrs() {
        let fixture = extract_contract_fixture();
        let reciprocal = fixture
            .empty_bundle_metadata
            .get("reciprocal")
            .expect("reciprocal metadata should be extracted with empty bundle");

        assert!(reciprocal.contracts.is_empty());
        assert!(reciprocal.spec.requires.is_empty());
        assert_eq!(reciprocal.contract_extraction.source, ContractExtractionSource::Unavailable);
        assert!(!reciprocal.contract_extraction.source_scraping_used);
        assert!(
            reciprocal
                .contract_extraction
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(
                    "native contract facts unavailable; compatibility source scraping disabled"
                )),
            "expected fail-closed diagnostic, got {:?}",
            reciprocal.contract_extraction.diagnostics
        );
    }

    #[test]
    fn native_no_contract_bundle_fails_closed_without_source_scraping() {
        let fixture = extract_contract_fixture();
        let no_contracts = fixture
            .metadata
            .get("no_contracts")
            .expect("no_contracts metadata should be extracted");

        assert!(no_contracts.contracts.is_empty());
        assert_eq!(no_contracts.contract_extraction.source, ContractExtractionSource::Unavailable);
        assert!(!no_contracts.contract_extraction.source_scraping_used);
        assert!(
            no_contracts
                .contract_extraction
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(
                    "native contract facts unavailable; compatibility source scraping disabled"
                )),
            "expected fail-closed diagnostic, got {:?}",
            no_contracts.contract_extraction.diagnostics
        );

        let function = fixture.functions.get("no_contracts").expect("function should be extracted");
        assert!(function.contracts.is_empty());
        assert_eq!(
            function.preconditions,
            vec![Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(i32::MIN.into())),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(i32::MAX.into())),
                ),
            ])],
            "only the tautological i32 parameter range should be present"
        );
        assert!(function.postconditions.is_empty());
    }

    #[test]
    fn extraction_demotes_generated_formula_parameter_names_without_contracts() {
        let fixture = extract_contract_fixture();
        let function = fixture
            .functions
            .get("generated_formula_name_params")
            .expect("generated-name fixture should be extracted");

        assert_eq!(function.body.locals[1].name.as_deref(), Some("s"));
        assert_eq!(function.body.locals[2].name, None);
        assert_eq!(function.body.locals[3].name, None);
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(1)), "s");
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(2)), "_2");
        assert_eq!(trust_vcgen::place_to_var_name(function, &Place::local(3)), "_3");
        assert_ne!(trust_vcgen::place_to_var_name(function, &Place::local(2)), "s__slice_len");
        assert_ne!(
            trust_vcgen::place_to_var_name(function, &Place::local(3)),
            trust_types::const_param_symbol(0, "N")
        );
    }

    #[test]
    fn real_mir_slice_last_preserves_slice_fat_pointer_shape() {
        let fixture = extract_contract_fixture();
        let function = fixture.functions.get("slice_last").expect("slice_last should be extracted");

        let arg = function
            .body
            .locals
            .iter()
            .find(|local| local.index == 1)
            .expect("slice_last slice argument local should be present");
        assert_eq!(
            arg.ty,
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
            "real rustc MIR slice argument must retain fat-pointer pointee shape"
        );
        assert_eq!(function.body.return_ty, Ty::u8());
        assert!(
            function.body.locals.iter().all(|local| !local.ty.is_unsupported()),
            "slice_last type extraction should not fail closed for ordinary slice shape: {:?}",
            function.body.locals
        );
        assert!(
            function.body.blocks.iter().flat_map(|block| &block.stmts).any(|stmt| {
                let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(place)), .. } = stmt
                else {
                    return false;
                };
                place.local == 1
                    && place.projections.contains(&Projection::Deref)
                    && place
                        .projections
                        .iter()
                        .any(|projection| matches!(projection, Projection::Index(_)))
            }),
            "slice_last should lower the real MIR indexed slice read without losing the slice local"
        );
    }

    #[test]
    fn option_return_type_lowers_to_explicit_tagged_adt() {
        let function = extract_option_return_fixture();

        let Ty::Adt { name, fields, .. } = &function.body.return_ty else {
            panic!(
                "expected Option return to lower as tagged ADT, got {:?}",
                function.body.return_ty
            );
        };
        assert!(
            name.ends_with("::option::Option") || name.ends_with("::Option"),
            "unexpected Option ADT path `{name}`"
        );
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0], ("__tag".to_string(), Ty::isize()));
        assert_eq!(fields[1], ("__v1_0".to_string(), Ty::i32()));
        assert!(
            function.body.locals.iter().all(|local| !local.ty.is_unsupported()),
            "Option lowering should not leave unsupported local types: {:?}",
            function.body.locals
        );
    }

    /// Lever A step 2 (real MIR): the kernel universe-`Level` enum extracts as a
    /// native recursive `Ty::Datatype` with its five real constructors and by-name
    /// `Level` self-references, NOT the recursive-ADT `Ty::Unsupported` degrade
    /// (the `Ty::Unsupported { kind: "TyKind::Adt", detail: "recursive …" }` shape
    /// this crate emits for un-modeled recursive ADTs). Def-path gated to `Level`.
    #[test]
    fn real_mir_clean_kernel_level_lowers_to_datatype() {
        let (level_ty, level_defs) = extract_level_datatype_fixture();

        assert!(
            !level_ty.is_unsupported(),
            "Level must not degrade to Unsupported, got {level_ty:?}"
        );
        // Trust: resolve the by-name marker through `datatype_defs`. Before the
        // body-de-duplication landing the variants were inline here; now the
        // occurrence is a marker and the one definition is filed in the side
        // table. Reading only the `Ty` asserts the pre-landing shape and fails.
        let (name, variants) = resolve_datatype(&level_ty, &level_defs);
        // Def paths render without the crate-name prefix for the crate under
        // compilation (`level::Level`) and with it for an upstream dependency
        // (`clean_kernel::level::Level`); accept either via suffix match.
        assert!(name.ends_with("level::Level"), "unexpected Level datatype name `{name}`");
        assert_eq!(variants.len(), 5, "Level has five constructors: {variants:?}");

        let field_list = |ctor: &str| -> &Vec<(String, Ty)> {
            variants
                .iter()
                .find(|(n, _)| n == ctor)
                .map(|(_, fs)| fs)
                .unwrap_or_else(|| panic!("missing constructor {ctor} in {variants:?}"))
        };
        // A by-name recursive `Level` self-reference: `Ty::Datatype` named `Level`
        // with an EMPTY variant list (the definitional occurrence is the outer type).
        let is_level_ref = |t: &Ty| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with("level::Level") && variants.is_empty()
            )
        };

        assert!(field_list("Zero").is_empty(), "Zero has no fields");

        let succ = field_list("Succ");
        assert_eq!(succ.len(), 1, "Succ has one Level field: {succ:?}");
        assert!(is_level_ref(&succ[0].1), "Succ field is a Level self-ref: {:?}", succ[0].1);

        for ctor in ["Max", "IMax"] {
            let fs = field_list(ctor);
            assert_eq!(fs.len(), 2, "{ctor} has two Level fields: {fs:?}");
            assert!(
                fs.iter().all(|(_, t)| is_level_ref(t)),
                "{ctor} fields are Level self-refs: {fs:?}"
            );
        }

        let param = field_list("Param");
        assert_eq!(param.len(), 1, "Param has one Name field: {param:?}");
        assert!(
            matches!(
                &param[0].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("name::Name") && variants.is_empty()
            ),
            "Param field is an opaque Name datatype ref: {:?}",
            param[0].1
        );
    }

    /// Lever A step 5 (real MIR): the kernel `ExprKind` enum — the type the real
    /// `infer_type` matches on — extracts as a native recursive `Ty::Datatype` with
    /// one constructor per variant, its recursive `Arc<Expr>` children as BY-NAME
    /// `Expr` refs, its `Sort` payload as a `Level` ref, and its `Name`/`Literal`/
    /// `BinderData` payloads as opaque datatype refs — NOT the recursive-ADT
    /// `Ty::Unsupported` / produced-node-budget degrade. Extraction is BOUNDED (the
    /// by-name refs keep the produced tree O(variants), dodging the 464 MB blow-up).
    #[test]
    fn real_mir_clean_kernel_exprkind_lowers_to_datatype() {
        let (exprkind_ty, _expr_ty, _defs) = extract_expr_datatypes_fixture();

        assert!(
            !exprkind_ty.is_unsupported(),
            "ExprKind must not degrade to Unsupported, got {exprkind_ty:?}"
        );
        let Ty::Datatype { name, variants } = &exprkind_ty else {
            panic!("ExprKind must lower to Ty::Datatype, got {exprkind_ty:?}");
        };
        assert!(
            name.ends_with("expr::kind::ExprKind"),
            "unexpected ExprKind datatype name `{name}`"
        );

        // BOUNDED-EXTRACTION EVIDENCE: with by-name refs the whole tree is a
        // handful of nodes. A full expansion (refs NOT used) would be thousands /
        // OOM, and a degrade would be `Unsupported` (asserted against above). A
        // small, exact node count proves the blow-up is dodged.
        let nodes = ty_total_node_count(&exprkind_ty, 100_000);
        assert!(
            nodes < 100,
            "ExprKind datatype must be BOUNDED (by-name refs, no expansion); got {nodes} nodes"
        );

        let field_list = |ctor: &str| -> &Vec<(String, Ty)> {
            variants
                .iter()
                .find(|(n, _)| n == ctor)
                .map(|(_, fs)| fs)
                .unwrap_or_else(|| panic!("missing constructor {ctor} in {variants:?}"))
        };
        // A by-name `Expr` self-reference: `Ty::Datatype` named `expr::Expr` with an
        // EMPTY variant list (its definition is the `Expr` datatype occurrence).
        let is_expr_ref = |t: &Ty| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with("expr::Expr") && variants.is_empty()
            )
        };
        let is_ref_ending = |t: &Ty, suffix: &str| {
            matches!(
                t,
                Ty::Datatype { name, variants }
                    if name.ends_with(suffix) && variants.is_empty()
            )
        };

        // Scalar payload: BVar(u32) → a real Int sort, not a datatype ref.
        let bvar = field_list("BVar");
        assert_eq!(bvar.len(), 1, "BVar has one u32 field: {bvar:?}");
        assert_eq!(bvar[0].1, Ty::Int { width: 32, signed: false }, "BVar payload is u32");

        // Sort(Level) → a by-name Level datatype ref (step-2 cross-reference).
        let sort = field_list("Sort");
        assert_eq!(sort.len(), 1, "Sort has one Level field: {sort:?}");
        assert!(
            is_ref_ending(&sort[0].1, "level::Level"),
            "Sort payload is a Level datatype ref: {:?}",
            sort[0].1
        );

        // Const(Name) → an opaque Name datatype ref.
        let konst = field_list("Const");
        assert!(
            is_ref_ending(&konst[0].1, "name::Name"),
            "Const payload is a Name datatype ref: {:?}",
            konst[0].1
        );

        // App(Expr, Expr) → two by-name Expr self-refs (the recursion, unexpanded).
        let app = field_list("App");
        assert_eq!(app.len(), 2, "App has two Expr fields: {app:?}");
        assert!(app.iter().all(|(_, t)| is_expr_ref(t)), "App fields are Expr refs: {app:?}");

        // Lam(BinderData, Expr, Expr) → opaque BinderData ref + two Expr refs.
        let lam = field_list("Lam");
        assert_eq!(lam.len(), 3, "Lam has three fields: {lam:?}");
        assert!(
            is_ref_ending(&lam[0].1, "binder::BinderData"),
            "Lam[0] is a BinderData ref: {:?}",
            lam[0].1
        );
        assert!(
            is_expr_ref(&lam[1].1) && is_expr_ref(&lam[2].1),
            "Lam[1..] are Expr refs: {lam:?}"
        );

        // Let(Expr, Expr, Expr, bool) → three Expr refs + a real Bool.
        let let_ = field_list("Let");
        assert_eq!(let_.len(), 4, "Let has four fields: {let_:?}");
        assert!(
            is_expr_ref(&let_[0].1) && is_expr_ref(&let_[1].1) && is_expr_ref(&let_[2].1),
            "Let[0..3] are Expr refs: {let_:?}"
        );
        assert_eq!(let_[3].1, Ty::Bool, "Let's nonDep flag is a real Bool sort");

        // SProp → a nullary constructor (no fields).
        assert!(field_list("SProp").is_empty(), "SProp has no fields");

        // CubicalPath { ty, left, right } → a struct-style variant, three Expr refs
        // keyed by their SOURCE field names (not positional indices).
        let cpath = field_list("CubicalPath");
        assert_eq!(cpath.len(), 3, "CubicalPath has three fields: {cpath:?}");
        assert_eq!(
            cpath.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
            vec!["ty", "left", "right"],
            "CubicalPath fields keep their source names"
        );
        assert!(cpath.iter().all(|(_, t)| is_expr_ref(t)), "CubicalPath fields are Expr refs");
    }

    /// Lever A step 5 (real MIR): the kernel `Expr` struct extracts as a
    /// single-constructor `Ty::Datatype` whose `kind` field is a by-name `ExprKind`
    /// ref and whose `meta` field is an opaque `ExprMeta` ref — the OTHER half of
    /// the Expr↔ExprKind mutual recursion, both by-name so neither expands the other.
    #[test]
    fn real_mir_clean_kernel_expr_lowers_to_datatype() {
        let (_exprkind_ty, expr_ty, defs) = extract_expr_datatypes_fixture();

        assert!(!expr_ty.is_unsupported(), "Expr must not degrade to Unsupported, got {expr_ty:?}");
        // Trust: resolve through `datatype_defs` — `Expr` is recursive, hence a
        // canonical cut point, hence a by-name marker at this occurrence.
        let (name, variants) = resolve_datatype(&expr_ty, &defs);
        assert!(name.ends_with("expr::Expr"), "unexpected Expr datatype name `{name}`");

        // A struct is a ONE-constructor ADT (named after the struct itself).
        assert_eq!(variants.len(), 1, "Expr struct is a single-constructor datatype: {variants:?}");
        let (ctor_name, fields) = &variants[0];
        assert!(
            ctor_name.ends_with("Expr"),
            "sole constructor is named after the struct: {ctor_name}"
        );
        assert_eq!(fields.len(), 2, "Expr has kind + meta fields: {fields:?}");

        assert_eq!(fields[0].0, "kind", "first field is `kind`");
        assert!(
            matches!(
                &fields[0].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("expr::kind::ExprKind") && variants.is_empty()
            ),
            "Expr.kind is a by-name ExprKind ref (recursion NOT expanded): {:?}",
            fields[0].1
        );

        assert_eq!(fields[1].0, "meta", "second field is `meta`");
        assert!(
            matches!(
                &fields[1].1,
                Ty::Datatype { name, variants }
                    if name.ends_with("meta::ExprMeta") && variants.is_empty()
            ),
            "Expr.meta is an opaque ExprMeta datatype ref: {:?}",
            fields[1].1
        );

        // BOUNDED: root + kind ref + meta ref = a tiny tree.
        let nodes = ty_total_node_count(&expr_ty, 100_000);
        assert!(nodes < 20, "Expr datatype must be BOUNDED; got {nodes} nodes");
    }

    /// A discriminant-range precondition is `discr == t0 OR discr == t1 OR ...`
    /// (or a lone `discr == t0`): each disjunct equates a variable to an integer
    /// tag constant. This is the always-true enum-tag invariant that
    /// `enum_discriminant_range_preconditions` attaches so an exhaustive `match`
    /// discharges its `otherwise -> Unreachable` obligation.
    fn is_tag_equality(formula: &Formula) -> bool {
        matches!(
            formula,
            Formula::Eq(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(_, _) | Formula::SymVar(_, _))
                    && matches!(rhs.as_ref(), Formula::Int(_) | Formula::UInt(_))
        )
    }

    fn has_discriminant_range_precondition(preconditions: &[Formula]) -> bool {
        preconditions.iter().any(|formula| match formula {
            Formula::Or(disjuncts) => {
                !disjuncts.is_empty() && disjuncts.iter().all(is_tag_equality)
            }
            single => is_tag_equality(single),
        })
    }

    /// Regression: matching on a `&Enum` must attach the same discriminant-range
    /// precondition as matching the enum by value. A `match` on a reference lowers
    /// the switch's discriminant read as `discriminant((*r))` — a `Deref` projection
    /// on the source place. Before the by-ref fix, `enum_discriminant_range_preconditions`
    /// rejected that deref source and dropped the precondition, so the exhaustive-match
    /// `otherwise -> Unreachable` obligation false-failed for code like `area_ish(&Shape)`
    /// that is no worse than its by-value form.
    #[test]
    fn real_mir_enum_match_by_ref_matches_by_value_discriminant_precondition() {
        let fixture = extract_contract_fixture();
        let by_value = fixture
            .functions
            .get("trust_dir_by_value")
            .expect("trust_dir_by_value should be extracted");
        let by_ref = fixture
            .functions
            .get("trust_dir_by_ref")
            .expect("trust_dir_by_ref should be extracted");

        assert!(
            has_discriminant_range_precondition(&by_value.preconditions),
            "by-value enum match should carry a discriminant-range precondition, got {:?}",
            by_value.preconditions
        );
        assert!(
            has_discriminant_range_precondition(&by_ref.preconditions),
            "matching on &Enum must emit a discriminant-range precondition exactly as the \
             by-value form does, otherwise the exhaustive-match Unreachable obligation \
             false-fails; got {:?}",
            by_ref.preconditions
        );
        assert_eq!(
            by_value.preconditions, by_ref.preconditions,
            "the by-ref discriminant-range precondition must be identical to the by-value one \
             (same tag set, same single-assignment discriminant temp)"
        );
    }

    /// regression: an `enum as int` cast (here `d as u32`) reads the
    /// discriminant into a temp that does *not* drive an exhaustive-match
    /// `otherwise -> Unreachable` switch. The original
    /// `enum_discriminant_range_preconditions` only emitted the tag-range fact for
    /// switch-driving temps, so the cast result read as a free i64 and the
    /// cast-overflow VC (and any arithmetic on it) false-FAILed. After the
    /// generalization to *every* single-assignment discriminant temp, this function
    /// must carry the discriminant-range precondition exactly as a `match` does.
    #[test]
    fn real_mir_enum_as_int_cast_carries_discriminant_precondition() {
        let fixture = extract_contract_fixture();
        let cast = fixture
            .functions
            .get("trust_discr_as_int")
            .expect("trust_discr_as_int should be extracted");
        assert!(
            has_discriminant_range_precondition(&cast.preconditions),
            "an `enum as int` cast must carry a discriminant-range precondition even \
             without an exhaustive match, got {:?}",
            cast.preconditions
        );
    }
    // ---- Trust: projected-chain sorts, resolved per chain (phase 2b) ----

    fn leaf_adt(name: &str, fields: Vec<Ty>) -> Ty {
        Ty::Adt {
            arbitrary_precision: None,
            validity_wrapper: None,
            adt_kind: None,
            layout: None,
            name: name.into(),
            fields: fields.into_iter().enumerate().map(|(i, t)| (format!("f{i}"), t)).collect(),
            variants: Vec::new().into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        }
    }

    #[test]
    fn projected_leaf_sort_resolves_the_one_chain_a_name_spells() {
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let vec4 = leaf_adt("Vec4", vec![Ty::f64_ty(); 4]);
        let mat = |len: u64| leaf_adt("Mat", vec![Ty::Array { elem: Box::new(vec4.clone()), len }]);
        let params = vec![
            ("m".to_string(), mat(4)),
            ("r".to_string(), Ty::Ref { mutable: false, inner: Box::new(mat(4)) }),
            ("big".to_string(), mat(100)),
            ("flag".to_string(), Ty::Tuple(vec![Ty::Bool, Ty::Int { width: 32, signed: true }])),
        ];
        assert_eq!(projected_leaf_sort(&params, "m.0[3].2"), Some(f64_sort.clone()));
        assert_eq!(projected_leaf_sort(&params, "r*.0[0].1"), Some(f64_sort.clone()));
        assert_eq!(projected_leaf_sort(&params, "flag.0"), Some(Sort::Bool));
        assert_eq!(projected_leaf_sort(&params, "flag.1"), Some(Sort::Int));
        // Past the retired 64-lane enumeration: lane 99 of a 100-lane array.
        assert_eq!(projected_leaf_sort(&params, "big.0[99].3"), Some(f64_sort));
        // Not leaves, or not lanes: fail closed (the parsed sort stays).
        for name in [
            "m",           // a bare name is the signature entry's business
            "m.0",         // an array, not a leaf
            "m.0[3]",      // a struct, not a leaf
            "m.0[4].2",    // lane 4 of 4
            "m.0[03].2",   // not the canonical decimal spelling
            "m.1",         // no such field
            "r.0[0].1",    // a reference head needs the `*`
            "m*.0[0].1",   // a by-value head has no pointee
            "nobody.0",    // not a parameter
            "flag.0.0",    // below a scalar
        ] {
            assert_eq!(projected_leaf_sort(&params, name), None, "{name}");
        }
        // An enum is never walked (its field view is variant-dependent).
        let mut enum_ty = leaf_adt("E", vec![Ty::Bool]);
        if let Ty::Adt { variants, .. } = &mut enum_ty {
            *variants = vec![VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::Bool)],
            }]
            .into();
        }
        assert_eq!(projected_leaf_sort(&[("e".into(), enum_ty)], "e.0"), None);
        // The nesting depth still bounds the walk (type text, not a length).
        let mut deep = Ty::Bool;
        for _ in 0..PROJECTED_LEAF_DEPTH_LIMIT {
            deep = Ty::Tuple(vec![deep]);
        }
        let at_limit = format!("d{}", ".0".repeat(PROJECTED_LEAF_DEPTH_LIMIT as usize));
        assert_eq!(projected_leaf_sort(&[("d".into(), deep.clone())], &at_limit), Some(Sort::Bool));
        let over = Ty::Tuple(vec![deep]);
        let over_limit = format!("d{}", ".0".repeat(PROJECTED_LEAF_DEPTH_LIMIT as usize + 1));
        assert_eq!(projected_leaf_sort(&[("d".into(), over)], &over_limit), None);
    }

    // ---- Trust: def-contracts lane sort environment (caller-side Precondition VCs) ----

    #[test]
    fn def_lane_retype_keeps_float_sort_on_field_chain_vars() {
        // The def-contracts lane must NOT clobber a Float-sorted field-chain var
        // to Int: `self.0 <= 1.0e30` parses with `self.0` at Float{11,53} (the
        // parser's float coercion), and the signature environment carries only
        // the BARE param name `self`. The old `split_once('.')` arm forced
        // `self.0` to Int, mis-sorting the caller-side Precondition VC operand
        // (or failing the Bool sort check → requires fails closed). Field-chain
        // vars — dotted, deref-dotted, and bracketed — must keep parsed sorts,
        // mirroring the body lane.
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let mut signature_sorts = BTreeMap::new();
        signature_sorts.insert("self".to_string(), Sort::Int);
        signature_sorts.insert("self*".to_string(), Sort::Int);
        for chain in ["self.0", "self*.0.0", "self.0[3].1"] {
            let formula = Formula::Le(
                Box::new(Formula::Var(chain.to_string(), f64_sort.clone())),
                Box::new(Formula::FpConst {
                    bits: u128::from(1.0e30f64.to_bits()),
                    eb: 11,
                    sb: 53,
                }),
            );
            let typed = retype_source_contract_formula(formula, &signature_sorts);
            let Formula::Le(lhs, _) = typed else { panic!("retype must preserve shape") };
            assert_eq!(
                *lhs,
                Formula::Var(chain.to_string(), f64_sort.clone()),
                "field-chain var `{chain}` must keep its parsed Float sort"
            );
        }
    }

    #[test]
    fn def_lane_retype_still_resorts_bare_params_and_synthetics() {
        // Regression guards for what the fix must NOT change: a bare f64 param
        // name takes its signature sort at any depth (difference bounds), and a
        // synthetic `<param>_len` var still lands at Int.
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let mut signature_sorts = BTreeMap::new();
        signature_sorts.insert("near".to_string(), f64_sort.clone());
        signature_sorts.insert("far".to_string(), f64_sort.clone());
        signature_sorts.insert("arr".to_string(), Sort::Int);
        let formula = Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Sub(
                    Box::new(Formula::Var("near".to_string(), Sort::Int)),
                    Box::new(Formula::Var("far".to_string(), Sort::Int)),
                )),
                Box::new(Formula::FpConst {
                    bits: u128::from((-1.0e-6f64).to_bits()),
                    eb: 11,
                    sb: 53,
                }),
            ),
            Formula::Ge(
                Box::new(Formula::Var("arr__len".to_string(), Sort::Bool)),
                Box::new(Formula::Int(1)),
            ),
        ]);
        let typed = retype_source_contract_formula(formula, &signature_sorts);
        let Formula::And(items) = typed else { panic!("retype must preserve shape") };
        let Formula::Le(sub, _) = &items[0] else { panic!("Le expected") };
        let Formula::Sub(near, far) = sub.as_ref() else { panic!("Sub expected") };
        assert_eq!(**near, Formula::Var("near".to_string(), f64_sort.clone()));
        assert_eq!(**far, Formula::Var("far".to_string(), f64_sort));
        let Formula::Ge(len, _) = &items[1] else { panic!("Ge expected") };
        assert_eq!(**len, Formula::Var("arr__len".to_string(), Sort::Int));
    }
}

/// SPEC-FLOAT-EQ-STRUCTURAL-1: a compiler proposition `==` over float domains is
/// Rust `PartialEq` — IEEE `FpEq`, never structural `Eq` — and the conversion
/// still matches the re-parse of its canonical source text exactly.
#[cfg(test)]
mod spec_float_eq_conversion_tests {
    use rustc_middle::mir::trust_contract::{
        TrustContractKind, TrustContractPredicateKind, TrustContractProposition as Proposition,
        TrustContractPropositionDomain as Domain,
    };
    use rustc_span::Symbol;
    use trust_types::{Formula, Sort};

    use super::convert_trust_contract_predicate;

    const F64: Sort = Sort::Float { eb: 11, sb: 53 };

    fn f64_param(name: &str) -> Proposition {
        Proposition::Var { name: Symbol::intern(name), domain: Domain::Float { width: 64 } }
    }

    fn converted(text: &str, proposition: Proposition) -> Formula {
        let predicate =
            TrustContractPredicateKind::Typed { text: Symbol::intern(text), proposition };
        let (_, typed) =
            convert_trust_contract_predicate(0, TrustContractKind::Requires, &predicate)
                .expect("the typed proposition matches its canonical source spelling");
        typed.expect("a typed proposition converts to a typed formula").0
    }

    #[test]
    fn float_parameter_equality_converts_to_fp_eq() {
        rustc_span::create_default_session_globals_then(|| {
            let formula = converted(
                "__trust_lowered_compiler_contract__:x == y",
                Proposition::Eq(Box::new(f64_param("x")), Box::new(f64_param("y"))),
            );
            assert_eq!(
                formula,
                Formula::FpEq(
                    Box::new(Formula::Var("x".to_string(), F64)),
                    Box::new(Formula::Var("y".to_string(), F64)),
                )
            );
        });
    }

    #[test]
    fn float_literal_equality_converts_to_fp_eq() {
        rustc_span::create_default_session_globals_then(|| {
            let formula = converted(
                "__trust_lowered_compiler_contract__:x == 1.0",
                Proposition::Eq(
                    Box::new(f64_param("x")),
                    Box::new(Proposition::Float { bits: 1.0_f64.to_bits(), width: 64 }),
                ),
            );
            assert_eq!(
                formula,
                Formula::FpEq(
                    Box::new(Formula::Var("x".to_string(), F64)),
                    Box::new(Formula::FpConst {
                        bits: u128::from(1.0_f64.to_bits()),
                        eb: 11,
                        sb: 53
                    }),
                )
            );
        });
    }

    #[test]
    fn integer_equality_stays_structural() {
        rustc_span::create_default_session_globals_then(|| {
            let formula = converted(
                "__trust_lowered_compiler_contract__:x == 0",
                Proposition::Eq(
                    Box::new(Proposition::Var {
                        name: Symbol::intern("x"),
                        domain: Domain::MachineInt { width: 8, signed: false },
                    }),
                    Box::new(Proposition::Int(0)),
                ),
            );
            assert!(matches!(formula, Formula::Eq(..)), "{formula:?}");
        });
    }
}

#[cfg(test)]
mod wave487_perf_tests {
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::io;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};

    use super::*;

    #[test]
    fn wave487_fast_ty_and_body_local_memo_and_span_cache_match_uncached_oracle() {
        const PATH: &str = "wave487_parity_fixture.rs";
        const SRC: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "copy"]
pub trait Copy: Clone {}
#[lang = "clone"]
pub trait Clone {}

impl Clone for usize {}
impl Copy for usize {}
impl Clone for u32 {}
impl Copy for u32 {}
impl Clone for isize {}
impl Copy for isize {}
impl Clone for char {}
impl Copy for char {}
impl Clone for bool {}
impl Copy for bool {}
impl Clone for f64 {}
impl Copy for f64 {}
impl<'a, T: PointeeSized> Clone for &'a T {}
impl<'a, T: PointeeSized> Copy for &'a T {}
impl<T: PointeeSized> Clone for *const T {}
impl<T: PointeeSized> Copy for *const T {}

pub struct Pair(pub usize, pub char);
pub enum Choice {
    Empty,
    SomePair(Pair),
}
pub enum RecList {
    Nil,
    Cons(u32, *const RecList),
}

#[inline(never)]
pub fn touch(_s: &str, _xs: &[u16], _p: *const u64, _f: f64) -> bool {
    true
}

pub fn exercise(
    a: u32,
    b: isize,
    c: char,
    s: &str,
    xs: &[u16],
    p: *const u64,
    f: f64,
    ch: Choice,
    rl: RecList,
) -> (usize, bool) {
    let ok = touch(s, xs, p, f);
    let t1 = (a as usize, ok);
    let t2 = (t1.0, t1.1);
    let _ = (b, c);
    let tag = match ch {
        Choice::Empty => 0usize,
        Choice::SomePair(pair) => pair.0,
    };
    let rtag = match rl {
        RecList::Nil => 0usize,
        RecList::Cons(v, _) => v as usize,
    };
    let _ = rtag;
    (tag, t2.1)
}
"#;
        struct FixtureLoader;
        impl rustc_span::source_map::FileLoader for FixtureLoader {
            fn file_exists(&self, path: &Path) -> bool {
                path == Path::new(PATH)
            }
            fn read_file(&self, path: &Path) -> io::Result<String> {
                if self.file_exists(path) {
                    Ok(SRC.to_string())
                } else {
                    Err(io::Error::other("unexpected fixture path"))
                }
            }
            fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
                Err(io::Error::other("unexpected binary read"))
            }
            fn current_directory(&self) -> io::Result<PathBuf> {
                std::env::current_dir()
            }
        }
        #[derive(Default)]
        struct ParityProbe {
            checked: bool,
        }
        impl rustc_driver::Callbacks for ParityProbe {
            fn config(&mut self, config: &mut Config) {
                config.file_loader = Some(Box::new(FixtureLoader));
            }
            fn after_analysis<'tcx>(
                &mut self,
                _: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                tcx.sess.dcx().abort_if_errors();
                for owner in tcx.hir_body_owners() {
                    let did = owner.to_def_id();
                    if tcx.opt_item_name(did).map(|s| s.as_str() == "exercise") != Some(true) {
                        continue;
                    }
                    let body = tcx.optimized_mir(did);
                    let typing_env = body.typing_env(tcx);

                    for faithful in [false, true] {
                        let _fg = faithful.then(ty_convert::FaithfulScalarsGuard::enable);
                        let _defs_a = ty_convert::DatatypeDefScope::begin();
                        let _tups_a = tuple_layouts::TupleLayoutScope::begin();
                        let elem_a = elem_sizes::ElemSizeScope::begin(!faithful);
                        let mut oracle_tys = Vec::new();
                        let remaining_oracle = {
                            let _bg = trust_types::verify_budget::VerifyBudgetGuard::install(
                                None, 1_000,
                            );
                            for decl in &body.local_decls {
                                oracle_tys.push(ty_convert::convert_ty_in_env_uncached_for_test(
                                    tcx, typing_env, decl.ty,
                                ));
                            }
                            let mut rem = 0u64;
                            while !trust_types::verify_budget::budget_exhausted() {
                                rem += 1;
                            }
                            rem
                        };
                        let defs_oracle = ty_convert::take_collected_datatype_defs();
                        let tups_oracle = tuple_layouts::collected_tuple_layouts();
                        let elems_oracle = elem_a.take_table();
                        drop(elem_a);
                        drop(_tups_a);
                        drop(_defs_a);

                        let _defs_b = ty_convert::DatatypeDefScope::begin();
                        let _tups_b = tuple_layouts::TupleLayoutScope::begin();
                        let elem_b = elem_sizes::ElemSizeScope::begin(!faithful);
                        let mut fast_tys = Vec::new();
                        let remaining_fast = {
                            let _bg = trust_types::verify_budget::VerifyBudgetGuard::install(
                                None, 1_000,
                            );
                            let mut memo = ty_convert::BodyLocalTyMemo::default();
                            for decl in &body.local_decls {
                                fast_tys.push(memo.convert_local_ty(tcx, typing_env, decl.ty));
                            }
                            let mut rem = 0u64;
                            while !trust_types::verify_budget::budget_exhausted() {
                                rem += 1;
                            }
                            rem
                        };
                        let defs_fast = ty_convert::take_collected_datatype_defs();
                        let tups_fast = tuple_layouts::collected_tuple_layouts();
                        let elems_fast = elem_b.take_table();
                        drop(elem_b);
                        drop(_tups_b);
                        drop(_defs_b);

                        assert_eq!(fast_tys, oracle_tys, "faithful={faithful}");
                        assert_eq!(
                            remaining_fast, remaining_oracle,
                            "VERIFY_STEPS parity faithful={faithful}",
                        );
                        assert_eq!(defs_fast, defs_oracle, "datatype_defs faithful={faithful}");
                        assert_eq!(tups_fast, tups_oracle, "tuple_layouts faithful={faithful}");
                        for t in &fast_tys {
                            assert_eq!(
                                elems_fast.lower_bound(t),
                                elems_oracle.lower_bound(t),
                                "elem_sizes faithful={faithful} ty={t:?}",
                            );
                        }

                        // Mid-walk step exhaustion (`step_budget = 5`) must also match byte-for-byte.
                        let exhausted_oracle: Vec<Ty> = {
                            let _defs = ty_convert::DatatypeDefScope::begin();
                            let _tups = tuple_layouts::TupleLayoutScope::begin();
                            let _elem = elem_sizes::ElemSizeScope::begin(false);
                            let _bg =
                                trust_types::verify_budget::VerifyBudgetGuard::install(None, 5);
                            body.local_decls
                                .iter()
                                .map(|d| {
                                    ty_convert::convert_ty_in_env_uncached_for_test(
                                        tcx, typing_env, d.ty,
                                    )
                                })
                                .collect()
                        };
                        let exhausted_fast: Vec<Ty> = {
                            let _defs = ty_convert::DatatypeDefScope::begin();
                            let _tups = tuple_layouts::TupleLayoutScope::begin();
                            let _elem = elem_sizes::ElemSizeScope::begin(false);
                            let _bg =
                                trust_types::verify_budget::VerifyBudgetGuard::install(None, 5);
                            let mut memo = ty_convert::BodyLocalTyMemo::default();
                            body.local_decls
                                .iter()
                                .map(|d| memo.convert_local_ty(tcx, typing_env, d.ty))
                                .collect()
                        };
                        assert_eq!(
                            exhausted_fast, exhausted_oracle,
                            "mid-walk exhaustion parity faithful={faithful}",
                        );
                    }

                    // Cached span conversion across all blocks must match uncached block lowering.
                    let overflow_session =
                        convert::OptionalOverflowAssertBodySession::of(tcx, body, false);
                    let uncached_blocks: Vec<BasicBlock> = body
                        .basic_blocks
                        .iter_enumerated()
                        .map(|(bb, bb_data)| {
                            convert::convert_basic_block(
                                tcx,
                                bb,
                                bb_data,
                                Some(body),
                                Some(typing_env),
                                Some(did),
                                overflow_session.for_terminator(body, bb_data.terminator()),
                            )
                        })
                        .collect();
                    let mut span_cache = FxHashMap::default();
                    let cached_blocks: Vec<BasicBlock> = body
                        .basic_blocks
                        .iter_enumerated()
                        .map(|(bb, bb_data)| {
                            convert::convert_basic_block_cached(
                                tcx,
                                bb,
                                bb_data,
                                Some(body),
                                Some(typing_env),
                                Some(did),
                                overflow_session.for_terminator(body, bb_data.terminator()),
                                &mut span_cache,
                            )
                        })
                        .collect();
                    assert_eq!(
                        serde_json::to_string(&cached_blocks).unwrap(),
                        serde_json::to_string(&uncached_blocks).unwrap(),
                    );
                    assert!(!span_cache.is_empty());
                    self.checked = true;
                }
                Compilation::Stop
            }
        }
        let mut probe = ParityProbe::default();
        let args = vec![
            "rustc".into(),
            PATH.into(),
            "--crate-name".into(),
            "wave487_parity".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zmir-opt-level=0".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "-Ztrust-ir-lower=off".into(),
            "-Ztrust-verify=off".into(),
            "-Ainternal_features".into(),
        ];
        let res = rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(&args, &mut probe);
        });
        assert!(res.is_ok(), "parity fixture must compile");
        assert!(probe.checked, "exercise body must be checked");
    }

    fn oracle_integer_param_range_preconditions(vbody: &VerifiableBody) -> Vec<Formula> {
        if vbody.arg_count == 0 {
            return Vec::new();
        }
        let mut out = Vec::new();
        for decl in &vbody.locals {
            if decl.index < 1 || decl.index > vbody.arg_count {
                continue;
            }
            let Ty::Int { width, signed } = &decl.ty else {
                continue;
            };
            let (width, signed) = (*width, *signed);
            if width == 0 || width > 64 {
                continue;
            }
            let Some(name) = decl.name.as_deref() else {
                continue;
            };
            let name_unique = local_name_is_unique(&vbody.locals, name);
            let var_name = if name_unique { name.to_string() } else { format!("_{}", decl.index) };
            let (min, max): (i128, i128) = if signed {
                (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
            } else {
                (0, (1i128 << width) - 1)
            };
            let var = || Formula::var(&var_name, Sort::Int);
            out.push(Formula::And(vec![
                Formula::Ge(Box::new(var()), Box::new(Formula::Int(min))),
                Formula::Le(Box::new(var()), Box::new(Formula::Int(max))),
            ]));
        }
        for decl in &vbody.locals {
            if decl.index < 1 || decl.index > vbody.arg_count {
                continue;
            }
            let runtime_slice = match &decl.ty {
                Ty::Slice { .. } => true,
                Ty::Ref { inner, .. } => matches!(inner.as_ref(), Ty::Slice { .. }),
                _ => false,
            };
            let Some(name) = decl.name.as_deref().filter(|_| runtime_slice) else {
                continue;
            };
            let name_unique = local_name_is_unique(&vbody.locals, name);
            let base = if name_unique { name.to_string() } else { format!("_{}", decl.index) };
            out.push(Formula::Ge(
                Box::new(Formula::var(&format!("{base}__slice_len"), Sort::Int)),
                Box::new(Formula::Int(0)),
            ));
        }
        out
    }

    #[test]
    fn wave487_integer_param_range_preconditions_matches_two_pass_oracle_dense_and_sparse() {
        let slice_u8 = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
        };
        let mut locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Int { width: 32, signed: false }, name: Some("a".into()) },
            LocalDecl { index: 2, ty: slice_u8.clone(), name: Some("xs".into()) },
            LocalDecl { index: 3, ty: Ty::Int { width: 16, signed: true }, name: Some("sh".into()) },
            LocalDecl { index: 4, ty: Ty::Int { width: 128, signed: false }, name: Some("wide".into()) },
            LocalDecl { index: 5, ty: Ty::Slice { elem: Box::new(Ty::Bool) }, name: Some("sh_slice".into()) },
            LocalDecl { index: 6, ty: Ty::Int { width: 64, signed: false }, name: None },
        ];
        // Shadow `sh` and `sh_slice` on body temporaries, plus 64 extra unnamed temporaries.
        locals.push(LocalDecl {
            index: 7,
            ty: Ty::Int { width: 64, signed: true },
            name: Some("sh".into()),
        });
        locals.push(LocalDecl { index: 8, ty: Ty::Bool, name: Some("sh_slice".into()) });
        for idx in 9..73 {
            locals.push(LocalDecl {
                index: idx,
                ty: Ty::Int { width: 32, signed: false },
                name: None,
            });
        }

        let dense_body = VerifiableBody {
            locals: locals.clone(),
            blocks: Vec::new(),
            arg_count: 6,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        };
        assert_eq!(
            integer_param_range_preconditions(&dense_body),
            oracle_integer_param_range_preconditions(&dense_body),
        );

        // Also pin the <=2 named-parameter fast path (no lazy FxHashMap materialization).
        let narrow_body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Int { width: 8, signed: false }, name: Some("x".into()) },
                LocalDecl { index: 2, ty: slice_u8, name: Some("s".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("x".into()) },
            ],
            blocks: Vec::new(),
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        };
        assert_eq!(
            integer_param_range_preconditions(&narrow_body),
            oracle_integer_param_range_preconditions(&narrow_body),
        );

        // Sparse / reordered hand-built test body: fallback scan must still match oracle.
        locals.swap(2, 7);
        let sparse_body = VerifiableBody {
            locals,
            blocks: Vec::new(),
            arg_count: 6,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        };
        assert_eq!(
            integer_param_range_preconditions(&sparse_body),
            oracle_integer_param_range_preconditions(&sparse_body),
        );
    }

    #[test]
    fn wave487_local_write_counts_and_collapse_debug_name_rows_preserve_exact_semantics() {
        let vbody = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::Int { width: 32, signed: true }, name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place { local: 2, projections: Vec::new() },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::SetDiscriminant {
                        place: Place { local: 2, projections: Vec::new() },
                        variant_index: 0,
                    },
                    Statement::Deinit { place: Place { local: 5, projections: Vec::new() } },
                    Statement::StorageLive(1),
                ],
                terminator: Terminator::Call {
                    func: "callee".into(),
                    args: Vec::new(),
                    dest: Place { local: 0, projections: Vec::new() },
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
                    unwind: UnwindEdge::Unreachable,
                },
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        };
        let counts = local_write_counts(&vbody);
        assert_eq!(counts.get(0).copied(), Some(1));
        assert_eq!(counts.get(1).copied(), Some(0));
        assert_eq!(counts.get(2).copied(), Some(2));
        assert_eq!(counts.get(5).copied(), Some(1));

        let empty: &[(usize, &str)] = &[];
        assert!(collapse_debug_name_rows(empty).is_empty());
        let rows = [
            (1usize, "x"),
            (2usize, "shared"),
            (1usize, "last_on_1"),
            (3usize, "shared"),
            (4usize, "xs__slice_len"),
            (4usize, "clean_local"),
        ];
        let collapsed = collapse_debug_name_rows(&rows);
        assert_eq!(collapsed.get(&1).map(String::as_str), Some("last_on_1"));
        assert!(!collapsed.contains_key(&2));
        assert!(!collapsed.contains_key(&3));
        assert_eq!(collapsed.get(&4).map(String::as_str), Some("clean_local"));
    }

    #[test]
    fn wave497_whole_body_ty_memo_and_cut_cache_parity() {
        use std::io;
        use std::path::{Path, PathBuf};
        use std::sync::Arc;
        use rustc_driver::Compilation;
        use rustc_interface::Config;
        use rustc_interface::interface::Compiler;

        const PATH: &str = "wave497_parity.rs";
        const SRC: &str = r#"
#![feature(lang_items, no_core)]
#![no_core]
#![allow(dead_code)]

#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "copy"]
pub trait Copy: Clone {}
#[lang = "clone"]
pub trait Clone {}

impl Clone for u8 {}
impl Copy for u8 {}
impl Clone for u32 {}
impl Copy for u32 {}
impl Clone for u64 {}
impl Copy for u64 {}
impl Clone for i32 {}
impl Copy for i32 {}
impl Clone for usize {}
impl Copy for usize {}
impl Clone for bool {}
impl Copy for bool {}
impl<'a, T: PointeeSized> Clone for &'a T {}
impl<'a, T: PointeeSized> Copy for &'a T {}
impl<T: PointeeSized> Clone for *const T {}
impl<T: PointeeSized> Copy for *const T {}

pub enum Tree {
    Leaf(u32),
    Branch(*const Tree, *const Tree),
}
pub struct Frame {
    pub tree: Tree,
    pub pair: (u64, i32),
    pub tag: u8,
}
pub fn zero_arg_helper() -> Frame {
    let root = Tree::Leaf(7);
    Frame { tree: root, pair: (11, 3), tag: 2 }
}
pub fn whole_body_target(f: Frame, xs: &[Frame], flag: bool) -> u64 {
    let h = zero_arg_helper();
    let _ = xs;
    let base = match f.tree {
        Tree::Leaf(v) => v as u64,
        Tree::Branch(_, _) => f.pair.0,
    };
    if flag { base } else { h.tag as u64 }
}
"#;
        struct FixtureLoader;
        impl rustc_span::source_map::FileLoader for FixtureLoader {
            fn file_exists(&self, path: &Path) -> bool {
                path == Path::new(PATH)
            }
            fn read_file(&self, path: &Path) -> io::Result<String> {
                if self.file_exists(path) {
                    Ok(SRC.to_string())
                } else {
                    Err(io::Error::other("unexpected fixture path"))
                }
            }
            fn read_binary_file(&self, _: &Path) -> io::Result<Arc<[u8]>> {
                Err(io::Error::other("unexpected binary read"))
            }
            fn current_directory(&self) -> io::Result<PathBuf> {
                std::env::current_dir()
            }
        }
        #[derive(Default)]
        struct Wave497Probe {
            checked: usize,
        }
        impl rustc_driver::Callbacks for Wave497Probe {
            fn config(&mut self, config: &mut Config) {
                config.file_loader = Some(Box::new(FixtureLoader));
            }
            fn after_analysis<'tcx>(
                &mut self,
                _: &Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> Compilation {
                tcx.sess.dcx().abort_if_errors();
                for owner in tcx.hir_body_owners() {
                    let did = owner.to_def_id();
                    let Some(sym) = tcx.opt_item_name(did) else { continue };
                    let name = sym.as_str();
                    if name != "zero_arg_helper" && name != "whole_body_target" {
                        continue;
                    }
                    let body = tcx.optimized_mir(did);
                    for faithful in [false, true] {
                        let _fg = faithful.then(ty_convert::FaithfulScalarsGuard::enable);
                        for step_budget in [2_000u64, 6u64] {
                            let mut oracle_elems = trust_vcgen::ElemSizeTable::default();
                            let (oracle_fn, oracle_rem) = {
                                let _nomemo = ty_convert::DisableBodyTyMemoGuard::enable();
                                let _bg = trust_types::verify_budget::VerifyBudgetGuard::install(
                                    None,
                                    step_budget,
                                );
                                let f = extract_function_with_purpose_observed(
                                    tcx,
                                    body,
                                    None,
                                    ExtractionPurpose::Verification,
                                    None,
                                    (!faithful).then_some(&mut oracle_elems),
                                );
                                let mut rem = 0u64;
                                while !trust_types::verify_budget::budget_exhausted() {
                                    rem += 1;
                                }
                                (f, rem)
                            };

                            let mut fast_elems = trust_vcgen::ElemSizeTable::default();
                            let (fast_fn, fast_rem) = {
                                let _bg = trust_types::verify_budget::VerifyBudgetGuard::install(
                                    None,
                                    step_budget,
                                );
                                let f = extract_function_with_purpose_observed(
                                    tcx,
                                    body,
                                    None,
                                    ExtractionPurpose::Verification,
                                    None,
                                    (!faithful).then_some(&mut fast_elems),
                                );
                                let mut rem = 0u64;
                                while !trust_types::verify_budget::budget_exhausted() {
                                    rem += 1;
                                }
                                (f, rem)
                            };

                            assert_eq!(
                                serde_json::to_string(&fast_fn).unwrap(),
                                serde_json::to_string(&oracle_fn).unwrap(),
                                "fn={name} faithful={faithful} budget={step_budget}",
                            );
                            assert_eq!(
                                fast_rem, oracle_rem,
                                "VERIFY_STEPS parity fn={name} faithful={faithful} budget={step_budget}",
                            );
                            for decl in &fast_fn.body.locals {
                                assert_eq!(
                                    fast_elems.lower_bound(&decl.ty),
                                    oracle_elems.lower_bound(&decl.ty),
                                    "elem_sizes fn={name} faithful={faithful} ty={:?}",
                                    decl.ty,
                                );
                            }
                        }
                    }
                    self.checked += 1;
                }
                Compilation::Stop
            }
        }
        let mut probe = Wave497Probe::default();
        let args = vec![
            "rustc".into(),
            PATH.into(),
            "--crate-name".into(),
            "wave497_parity".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-Zmir-opt-level=0".into(),
            "-Zno-codegen".into(),
            "-Zcodegen-backend=dummy".into(),
            "-Ztrust-ir-lower=off".into(),
            "-Ztrust-verify=off".into(),
            "-Ainternal_features".into(),
        ];
        let res = rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(&args, &mut probe);
        });
        assert!(res.is_ok(), "wave497 parity fixture must compile");
        assert_eq!(probe.checked, 2, "both zero-arg and parameterized bodies must be checked");
    }

    #[test]
    fn wave502_lazy_contract_sort_env_and_retype_preserve_exact_semantics() {
        let f64_sort = Sort::Float { eb: 11, sb: 53 };
        let mut base_sorts = std::collections::BTreeMap::new();
        base_sorts.insert("x".to_string(), f64_sort.clone());
        base_sorts.insert("xs".to_string(), Sort::Int);

        // 1. Scalar/slice-only signature: `contract_sort_environment_for_clauses` borrows
        // `signature.sorts` without cloning or pre-parsing clauses.
        let scalar_sig = ContractSignatureEnvironment {
            sorts: base_sorts.clone(),
            parameters: vec![
                ("x".to_string(), Ty::f64_ty()),
                ("xs".to_string(), Ty::Slice { elem: Box::new(Ty::Int { width: 32, signed: true }) }),
            ],
        };
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                body: "x > 0.0".to_string(),
                span: SourceSpan::default(),
            },
            Contract {
                kind: ContractKind::Ensures,
                body: "result >= old_x".to_string(),
                span: SourceSpan::default(),
            },
        ];
        let empty_bundle = trust_types::CompilerContractBundle::default();
        let (cow_sorts, cached) =
            contract_sort_environment_for_clauses(&scalar_sig, &contracts, &empty_bundle);
        assert!(matches!(cow_sorts, std::borrow::Cow::Borrowed(_)));
        assert!(cached.is_empty());

        // 2. Projectable struct parameter: `contract_sort_environment_for_clauses` upgrades
        // `Cow` only when a projected leaf (`pair.0`) is resolved and caches normalized/parsed clauses.
        let tuple_sig = ContractSignatureEnvironment {
            sorts: base_sorts.clone(),
            parameters: vec![(
                "pair".to_string(),
                Ty::Tuple(vec![Ty::f64_ty(), Ty::Bool]),
            )],
        };
        let proj_contracts = vec![Contract {
            kind: ContractKind::Requires,
            body: "pair.0 > 0.0".to_string(),
            span: SourceSpan::default(),
        }];
        let (proj_sorts, proj_cached) =
            contract_sort_environment_for_clauses(&tuple_sig, &proj_contracts, &empty_bundle);
        assert!(matches!(proj_sorts, std::borrow::Cow::Owned(_)));
        assert_eq!(proj_sorts.get("pair.0"), Some(&f64_sort));
        assert_eq!(proj_cached.len(), 1);
        assert!(proj_cached[0].is_some());

        // 3. `retype_source_contract_formula`: zero-clone fast path when no `old_*` or synthetic
        // suffix appears, and lazy map extension when `old_x` / `xs__len` appears.
        let plain_formula = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let retyped_plain = retype_source_contract_formula(plain_formula, &base_sorts);
        assert_eq!(
            retyped_plain,
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), f64_sort.clone())),
                Box::new(Formula::Int(0)),
            )
        );

        let synthetic_formula = Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::Var("old_x".to_string(), Sort::Int)),
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
            ),
            Formula::Ge(
                Box::new(Formula::Var("xs__len".to_string(), Sort::Bool)),
                Box::new(Formula::Int(1)),
            ),
        ]);
        let retyped_syn = retype_source_contract_formula(synthetic_formula, &base_sorts);
        assert_eq!(
            retyped_syn,
            Formula::And(vec![
                Formula::FpEq(
                    Box::new(Formula::Var("old_x".to_string(), f64_sort.clone())),
                    Box::new(Formula::Var("x".to_string(), f64_sort)),
                ),
                Formula::Ge(
                    Box::new(Formula::Var("xs__len".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                ),
            ])
        );
    }
}

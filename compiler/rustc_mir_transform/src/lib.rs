// tidy-alphabetical-start
#![feature(const_type_name)]
#![feature(cow_is_borrowed)]
#![feature(deref_patterns)]
#![feature(impl_trait_in_assoc_type)]
#![feature(iterator_try_collect)]
#![feature(option_into_flat_iter)]
#![feature(try_blocks)]
#![feature(yeet_expr)]
// tidy-alphabetical-end

use hir::ConstContext;
use required_consts::RequiredConstsVisitor;
use rustc_const_eval::check_consts::{self, ConstCx};
use rustc_const_eval::util;
use rustc_data_structures::fx::FxIndexSet;
use rustc_data_structures::steal::Steal;
use rustc_hir as hir;
use rustc_hir::def::{CtorKind, DefKind};
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    AnalysisPhase, BindingForm, Body, CallSource, ClearCrossCrate, ConstOperand, ConstQualifs,
    LocalDecl, LocalInfo, MirPhase, Operand, Place, ProjectionElem, Promoted, RuntimePhase, Rvalue,
    START_BLOCK, SourceInfo, Statement, StatementKind, TerminatorKind, WithRetag,
};
use rustc_middle::query;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypingEnv};
use rustc_middle::util::Providers;
use rustc_span::{DUMMY_SP, Spanned, bug, span_bug, sym};
use tracing::debug;

#[macro_use]
mod pass_manager;

use std::sync::LazyLock;

use pass_manager::{self as pm, Lint, MirLint, MirPass, PassCtx, PassPolicy, WithMinOptLevel};

mod canonicalization;
mod check_pointers;
// Trust: cross-crate PROOF-position citation — gathering the dependency crates
// that transported Clean proof material, and the v7/D3 notes that say so. It
// composes nothing and changes no verdict; see its header.
mod clean_extern_proof;
// Trust (I5): the SOLE CONSTRUCTOR of a Clean-origin `Body`, and the
// carrier-typed faithfulness gate that stands in front of it. This is the one
// direction in Trust that produces a value, so a disagreement is a wrong
// binary; read that file's header before touching any of its five call sites
// (`mir_keys`, `inner_optimized_mir`, `inner_mir_for_ctfe`, `promoted_mir`,
// `mir_drops_elaborated_and_const_checked`).
mod clean_origin_mir;
pub mod clean_origin_references;
// Trust: (IR-1) — the Clean-origin trust-ir RECORDING PATH: finalize-seam
// collection with a re-earned kernel verdict per def, feeding the per-crate
// direct Module (docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3).
// `pub` because `rustc_interface::passes` drives it at the finalize seam.
pub mod clean_origin_ir;
// Trust: (I7) — Clean-origin verdict-digest EXPORT providers (encode half).
mod clean_origin_export;
// Trust: D-2 logical faces; independent of verification_enabled.
mod trust_odt;
// Trust: TG11 interim MIR reader; the C1/C2 provider above stays MIR-free.
mod trust_odt_e6;
// Trust: (I7) — Clean-origin cross-crate IMPORT lane (readmission + re-gate).
mod clean_origin_import;
mod cost_checker;
mod cross_crate_inline;
mod deduce_param_attrs;
mod diagnostics;
mod elaborate_drop;
mod ffi_unwind_calls;
mod lint;
mod lint_tail_expr_drop_order;
mod liveness;
mod patch;
mod shim;
mod ssa;
mod trivial_const;
mod trust_contract_query;
// Trust: P1 item 5 — the trust-ir flip: `inner_optimized_mir` consumes MIR derived from the
// green (DerivedAgreed) trust-ir Module. See trust_ir_flip.rs for the full design notes.
// Trust (wall A): the per-INSTANCE trust-ir flip — the codegen-seam lane for GENERIC bodies the
// `optimized_mir` seam cannot flip. See trust_instance_flip.rs.
mod trust_instance_flip;
mod trust_ir_flip;
pub mod trust_lean_census;
mod trust_lean_census_order;
// Trust: the once-initializer re-entrancy check — a hard error, gated by nothing but
// front-end cleanliness (NOT by `-Ztrust-verify`). Driver entry point exported below.
mod trust_once_reentrancy;
mod trust_proof_query;
mod trust_r1_oracle;
// Trust (D4 increment A, 2026-09-24): the per-def "contains user `unsafe` source" fact,
// computed here from HIR and encoded in rmeta so a consumer re-deriving the body from its
// encoded MIR can decline it. See trust_unsafe_source_fact.rs.
mod trust_unsafe_source_fact;
// Trust (v6/D1): the `targo trust spec --emit clean` session-artifact writer.
// `pub` so the emit surface is externally reachable (and warning-free) even
// before/without the trust_verify.rs call sites that feed it.
pub mod trust_spec_emit;

/// Exposed for rustc drivers.
pub use shim::build_drop_shim;

/// We import passes via this macro so that we can have a static list of pass names
/// (used to verify CLI arguments). It takes a list of modules, followed by the passes
/// declared within them.
/// ```ignore,macro-test
/// declare_passes! {
///     // Declare a single pass from the module `abort_unwinding_calls`
///     mod abort_unwinding_calls : AbortUnwindingCalls;
///     // When passes are grouped together as an enum, declare the two constituent passes
///     mod add_call_guards : AddCallGuards {
///         AllCallEdges,
///         CriticalCallEdges
///     };
///     // Declares multiple pass groups, each containing their own constituent passes
///     mod simplify : SimplifyCfg {
///         Initial,
///         /* omitted */
///     }, SimplifyLocals {
///         BeforeConstProp,
///         /* omitted */
///     };
/// }
/// ```
macro_rules! declare_passes {
    (
        $(
            $vis:vis mod $mod_name:ident : $($pass_name:ident $( { $($ident:ident),* } )?),+ $(,)?;
        )*
    ) => {
        $(
            $vis mod $mod_name;
            $(
                // Make sure the type name is correct
                #[allow(unused_imports)]
                use $mod_name::$pass_name as _;
            )+
        )*

        static PASS_NAMES: LazyLock<FxIndexSet<&str>> = LazyLock::new(|| {
            let mut set = FxIndexSet::default();
            $(
                $(
                    set.extend(pass_names!($mod_name : $pass_name $( { $($ident),* } )? ));
                )+
            )*
            set
        });
    };
}

macro_rules! pass_names {
    // pass groups: only pass names inside are considered pass_names
    ($mod_name:ident : $pass_group:ident { $($pass_name:ident),* $(,)? }) => {
        [
            $(
                $mod_name::$pass_group::$pass_name.name(),
            )*
        ]
    };
    // lone pass names: stringify the struct or enum name
    ($mod_name:ident : $pass_name:ident) => {
        [stringify!($pass_name)]
    };
}

declare_passes! {
    mod abort_unwinding_calls : AbortUnwindingCalls;
    mod add_call_guards : AddCallGuards { AllCallEdges, CriticalCallEdges };
    mod add_moves_for_packed_drops : AddMovesForPackedDrops;
    mod add_subtyping_projections : Subtyper;
    mod check_inline : CheckForceInline;
    mod check_call_recursion : CheckCallRecursion, CheckDropRecursion;
    mod check_alignment : CheckAlignment;
    mod check_enums : CheckEnums;
    mod check_const_item_mutation : CheckConstItemMutation;
    mod check_null : CheckNull;
    mod check_packed_ref : CheckPackedRef;
    mod check_mut_restriction : CheckMutRestriction;
    // This pass is public to allow external drivers to perform MIR cleanup
    pub mod cleanup_post_borrowck : CleanupPostBorrowck;

    mod copy_prop : CopyProp;
    mod coroutine : StateTransform;
    mod coverage : InstrumentCoverage;
    mod ctfe_limit : CtfeLimit;
    mod dataflow_const_prop : DataflowConstProp;
    mod dead_store_elimination : DeadStoreElimination {
        Initial,
        Final
    };
    mod deref_separator : Derefer;
    mod dest_prop : DestinationPropagation;
    mod early_otherwise_branch : EarlyOtherwiseBranch;
    mod erase_deref_temps : EraseDerefTemps;
    mod elaborate_box_derefs : ElaborateBoxDerefs;
    mod elaborate_drops : ElaborateDrops;
    mod function_item_references : FunctionItemReferences;
    mod gvn : GVN;
    // Made public so that `mir_drops_elaborated_and_const_checked` can be overridden
    // by custom rustc drivers, running all the steps by themselves. See #114628.
    pub mod inline : Inline, ForceInline;
    mod impossible_clauses : ImpossibleClauses;
    mod instsimplify : InstSimplify { BeforeInline, AfterSimplifyCfg };
    mod jump_threading : JumpThreading;
    mod known_panics_lint : KnownPanicsLint;
    mod lint_and_remove_uninhabited : LintAndRemoveUninhabited;
    mod lower_intrinsics : LowerIntrinsics;
    mod lower_slice_len : LowerSliceLenCalls;
    mod match_branches : MatchBranchSimplification;
    mod mentioned_items : MentionedItems;
    mod move_elimination : MoveElimination;
    mod multiple_return_terminators : MultipleReturnTerminators;
    mod post_drop_elaboration : CheckLiveDrops;
    mod prettify : ReorderBasicBlocks, ReorderLocals;
    mod promote_consts : PromoteTemps;
    // Trust: rust-lang#127553 — eliminate bounds checks dominated by an identical check.
    mod redundant_bounds_check : RedundantBoundsCheckElim;
    mod ref_prop : ReferencePropagation;
    mod remove_noop_landing_pads : RemoveNoopLandingPads;
    mod remove_place_mention : RemovePlaceMention;
    mod remove_storage_markers : RemoveStorageMarkers;
    mod remove_uninit_drops : RemoveUninitDrops;
    mod remove_unneeded_drops : RemoveUnneededDrops;
    mod remove_zsts : RemoveZsts;
    mod required_consts : RequiredConstsVisitor;
    mod post_analysis_normalize : PostAnalysisNormalize;
    mod sanity_check : SanityCheck;
    // This pass is public to allow external drivers to perform MIR cleanup
    pub mod simplify :
        SimplifyCfg {
            Initial,
            PromoteConsts,
            RemoveFalseEdges,
            PostAnalysis,
            PreOptimizations,
            Final,
            MakeShim,
            AfterUnreachableEnumBranching
        },
        SimplifyLocals {
            BeforeConstProp,
            AfterGVN,
            Final
        };
    mod simplify_branches : SimplifyConstCondition {
        AfterInstSimplify,
        AfterConstProp,
        Final
    };
    mod simplify_comparison_integral : SimplifyComparisonIntegral;
    mod single_use_consts : SingleUseConsts;
    mod sroa : ScalarReplacementOfAggregates;
    mod strip_debuginfo : StripDebugInfo;
    mod ssa_range_prop: SsaRangePropagation;
    mod tail_copy_to_move : TailCopyToMove;
    mod trust_verify : TrustVerify;
    mod unreachable_enum_branching : UnreachableEnumBranching;
    mod unreachable_prop : UnreachablePropagation;
    mod validate : Validator;
}

// Trust: expose the analysis-phase backing-certificate initializer to the driver
// (`rustc_interface::passes::analysis`). Computes interprocedural backing-struct
// certificates while post-analysis MIR is still borrowable (pre-steal).
// Trust: end-of-compile structured coverage inventory for each rustc target.
// Trust (scope-truncation fix): expose the eager whole-crate `optimized_mir` demand
// to the driver (`rustc_interface::passes::analysis`). Makes verification COVERAGE
// independent of diagnostic ordering: one function's verification error can never
// prevent another function from being verified.
// Trust #540 (R1): preserve the analysis-phase initialization seam while the
// strengthening authority remains hard-disabled. The exported initializer
// records no flip capability until a non-forgeable authority lane exists.
// Trust (lane CTFE): the trivial-const flip probe. MEASUREMENT ONLY — gated on
// `-Ztrust-ctfe-trivial-probe`, installs no body, changes no emitted code.
pub use trust_ir_flip::probe_trivial_const_flips as trust_probe_trivial_const_flips;
pub use trust_once_reentrancy::trust_check_once_initializer_reentrancy;
// Trust (2026-10-18, FRESH-CAPTURE-1): the pre-steal fresh shared closure capture seam.
pub use trust_verify::trust_init_fresh_capture_premises;
// Trust (D2 tier 1): the pre-steal ADAPTER_YIELD premise initializer.
// Trust (2026-09-29): the analysis-seam call-graph oracle force and the verified-lane
// coroutine `optimized_mir` sweep (see `trust_local_coroutine_layout`).
pub use trust_verify::{
    // Trust: current-source diagnostic measurement; no reusable facts returned.
    TrustConstructorAdmissionProbe,
    TrustConstructorAdmissionRefusal,
    TrustConstructorIdentityRefusal,
    // Trust (TG3): rustdoc's kernel-obligation entry.
    trust_check_kernel_obligations_for_rustdoc,
    trust_constructor_return_admission_probe,
    trust_emit_transport_crate_summary,
    trust_ensure_coroutine_optimized_mir,
    trust_ensure_whole_crate_verification,
    trust_finalize_calculus_reporting,
    trust_finalize_calculus_reporting_on_error,
    trust_force_crate_graph_oracles,
    trust_init_adapter_yield_premises,
    trust_init_backing_certificates,
    // Trust (STR_BYTE_POSITION): the byte-position closure certificate seam.
    trust_init_byte_eq_predicates,
    trust_init_calculus_reporting,
    trust_init_r1_attributions,
    trust_spawn_census_shadow,
};

/// Trust (wall A): emit the per-INSTANCE flip census at the post-codegen seam. A no-op unless the
/// instance lane is enabled. Re-exported because `rustc_interface` owns that seam and cannot
/// reach a private module here.
pub fn trust_instance_flip_census(tcx: TyCtxt<'_>) {
    trust_instance_flip::emit_census(tcx);
}

pub fn provide(providers: &mut Providers) {
    coverage::query::provide(providers);
    ffi_unwind_calls::provide(&mut providers.queries);
    shim::provide(&mut providers.queries);
    cross_crate_inline::provide(&mut providers.queries);
    providers.hooks.find_noop_landing_pads_for_instance =
        remove_noop_landing_pads::find_noop_landing_pads_for_instance;
    providers.queries = query::Providers {
        mir_keys,
        mir_built,
        mir_const_qualif,
        mir_promoted,
        mir_drops_elaborated_and_const_checked,
        mir_for_trust_verification,
        // Trust: the pre-steal local coroutine layout (`ordinary_coroutine_layout`).
        trust_local_coroutine_layout: trust_verify::trust_local_coroutine_layout,
        // Trust: the once-initializer check's vanilla-optimized coroutine view.
        trust_once_coroutine_mir,
        trust_instance_flip_body: trust_instance_flip::trust_instance_flip_body,
        trust_clean_origin_references: clean_origin_references::references,
        // Trust: the Clean purity guard's pre-steal per-body fact.
        trust_rust_purity_fact: clean_origin_mir::rust_purity_fact,
        trust_mir_direct_local_callees: trust_verify::trust_mir_direct_local_callees,
        trust_mir_mutually_recursive_functions:
            trust_verify::trust_mir_mutually_recursive_functions,
        // Trust (TG16): the HIR-only kernel-obligation predicate that rustdoc's
        // kernel lane and the vanilla `-O` MIR level pin both read.
        trust_crate_has_kernel_obligations: trust_verify::trust_crate_has_kernel_obligations,
        // Trust: the spawn census on trust-ir's reachability engine (design
        // 2026-09-29-spawn-census-by-construction), and its per-body projection.
        trust_spawn_census: trust_verify::trust_spawn_census,
        trust_spawn_sites: trust_verify::trust_spawn_sites,
        // Trust (PKG-C5d): the span-free `mentioned_items` of a body's optimized
        // MIR; the extern half reads the producer's `trust_mentioned_items` table.
        trust_mentioned_items: |tcx, def| {
            tcx.optimized_mir(def)
                .mentioned_items
                .as_ref()
                .map(|items| items.iter().map(|item| item.node).collect())
        },
        trust_mir_once_body_facts: trust_once_reentrancy::trust_mir_once_body_facts,
        mir_for_ctfe,
        mir_coroutine_witnesses: coroutine::mir_coroutine_witnesses,
        optimized_mir,
        check_liveness: liveness::check_liveness,
        is_mir_available,
        mir_callgraph_cyclic: inline::cycle::mir_callgraph_cyclic,
        mir_inliner_callees: inline::cycle::mir_inliner_callees,
        promoted_mir,
        deduced_param_attrs: deduce_param_attrs::deduced_param_attrs,
        coroutine_by_move_body_def_id: coroutine::coroutine_by_move_body_def_id,
        trivial_const: trivial_const::trivial_const,
        trust_contracts: trust_contract_query::trust_contracts,
        trust_proof_results: trust_proof_query::trust_proof_results,
        trust_proof_telemetry: trust_proof_query::trust_proof_telemetry,
        // Trust: (I7) — Clean-origin cross-crate ENCODE lane.
        trust_clean_verdict_digest: clean_origin_export::trust_clean_verdict_digest,
        // Trust: ODT source transport and cached local/extern B1 admission.
        trust_odt_entry: trust_odt::odt_entry,
        trust_odt_logical_face: trust_odt::logical_face,
        trust_clean_island_sources: clean_origin_export::trust_clean_island_sources,
        trust_clean_origin_exports: clean_origin_export::trust_clean_origin_exports,
        // Trust: cross-crate PROOF-position citation, increment 2 (TRANSPORT) — the
        // manifest that identifies the island sources above for a dependent crate.
        trust_clean_proof_manifest: clean_origin_export::trust_clean_proof_manifest,
        // Trust (2026-10-03): the per-crate "may install an allocation-error hook"
        // fact, encoded into metadata for downstream whole-program compilations.
        trust_crate_references_alloc_error_hook:
            trust_verify::trust_crate_references_alloc_error_hook_local,
        // Trust (T6): the per-crate "MIR built by the proof-session -O0 pipeline"
        // fact, encoded into metadata for verified dependents' re-derivation.
        trust_crate_mir_is_proof_session_pipeline:
            trust_verify::trust_crate_mir_is_proof_session_pipeline_local,
        // Trust: (I7) — Clean-origin cross-crate IMPORT lane: readmission at the
        // extern MIR decode chokepoint (rustc_metadata's cstore arms ensure this
        // query before serving a listed def's body), plus the bug!-on-local arms
        // of the decode-only accessors the readmission re-gate uses.
        trust_clean_extern_readmission: clean_origin_import::trust_clean_extern_readmission,
        trust_clean_extern_unreadmitted_optimized_mir:
            clean_origin_import::local_unreadmitted_optimized_mir,
        trust_clean_extern_unreadmitted_mir_for_ctfe:
            clean_origin_import::local_unreadmitted_mir_for_ctfe,
        // Trust (D4 increment A, 2026-09-24): the local half of the user-`unsafe`
        // source fact; the extern half decodes rmeta and answers `true` for a
        // missing row.
        trust_def_has_user_unsafe_source:
            trust_unsafe_source_fact::trust_def_has_user_unsafe_source,
        // Trust (CB3, 2026-09-28): the local half of the per-def island marker
        // (HIR item kind); the extern half decodes rmeta and answers `false` —
        // "real global assembly" — for a missing row.
        trust_def_is_clean_island: clean_origin_export::trust_def_is_clean_island,
        ..providers.queries
    };
}

fn remap_mir_for_const_eval_select<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut body: Body<'tcx>,
    context: hir::Constness,
) -> Body<'tcx> {
    for bb in body.basic_blocks.as_mut_preserves_cfg().iter_mut() {
        let terminator = bb.terminator.as_mut().expect("invalid terminator");
        match terminator.kind {
            TerminatorKind::Call {
                func: Operand::Constant(ConstOperand { ref const_, .. }),
                ref mut args,
                destination,
                target,
                unwind,
                fn_span,
                ..
            } if let ty::FnDef(def_id, _) = *const_.ty().kind()
                && tcx.is_intrinsic(def_id, sym::const_eval_select) =>
            {
                let Ok([tupled_args, called_in_const, called_at_rt]) = take_array(args) else {
                    unreachable!()
                };
                let ty = tupled_args.node.ty(&body.local_decls, tcx);
                let fields = ty.tuple_fields();
                let num_args = fields.len();
                let func = match context {
                    // Using `const_eval_select` in always-const code is useful when used in macros
                    // that you don't know whether they are going to be used in `const fn` or in `const` items.
                    hir::Constness::Const { .. } => called_in_const,
                    hir::Constness::NotConst => called_at_rt,
                };
                let (method, place): (fn(Place<'tcx>) -> Operand<'tcx>, Place<'tcx>) =
                    match tupled_args.node {
                        Operand::Constant(_) | Operand::RuntimeChecks(_) => {
                            // There is no good way of extracting a tuple arg from a constant
                            // (const generic stuff) so we just create a temporary and deconstruct
                            // that.
                            let local = body.local_decls.push(LocalDecl::new(ty, fn_span));
                            bb.statements.push(Statement::new(
                                SourceInfo::outermost(fn_span),
                                StatementKind::Assign(Box::new((
                                    local.into(),
                                    Rvalue::Use(tupled_args.node.clone(), WithRetag::Yes),
                                ))),
                            ));
                            (Operand::Move, local.into())
                        }
                        Operand::Move(place) => (Operand::Move, place),
                        Operand::Copy(place) => (Operand::Copy, place),
                    };
                let place_elems = place.projection;
                let arguments = (0..num_args)
                    .map(|x| {
                        let projection = tcx.mk_place_elems_from_iter(
                            place_elems
                                .iter()
                                .chain([ProjectionElem::Field(x.into(), fields[x])]),
                        );
                        let place = Place { local: place.local, projection };
                        Spanned { node: method(place), span: DUMMY_SP }
                    })
                    .collect();
                terminator.kind = TerminatorKind::Call {
                    func: func.node,
                    args: arguments,
                    destination,
                    target,
                    unwind,
                    call_source: CallSource::Misc,
                    fn_span,
                };
            }
            _ => {}
        }
    }
    body
}

fn take_array<T, const N: usize>(b: &mut Box<[T]>) -> Result<[T; N], Box<[T]>> {
    let b: Box<[T; N]> = std::mem::take(b).try_into()?;
    Ok(*b)
}

fn is_mir_available(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    tcx.mir_keys(()).contains(&def_id)
}

/// Finds the full set of `DefId`s within the current crate that have
/// MIR associated with them.
fn mir_keys(tcx: TyCtxt<'_>, (): ()) -> FxIndexSet<LocalDefId> {
    let owners = tcx.hir_body_owners();
    let mut set = FxIndexSet::with_capacity_and_hasher(owners.size_hint().0, Default::default());
    let mut closures = Vec::new();

    // All body-owners have MIR associated with them, except fake bodies for
    // `global_asm!`, which are not useful to emit (`--emit=mir`) or encode (in metadata).
    for body_owner in owners {
        match tcx.def_kind(body_owner) {
            DefKind::GlobalAsm => continue,
            DefKind::Closure => {
                set.insert(body_owner);
                closures.push(body_owner);
            }
            _ => {
                set.insert(body_owner);
            }
        }
    }

    // Coroutine-closures (e.g. async closures) have an additional by-move MIR
    // body that isn't in the HIR.
    for body_owner in closures {
        if tcx.needs_coroutine_by_move_body_def_id(body_owner.to_def_id()) {
            set.insert(tcx.coroutine_by_move_body_def_id(body_owner).expect_local());
        }
    }

    // tuple struct/variant constructors have MIR, but they don't have a BodyId,
    // so we need to build them separately.
    for item in tcx.hir_crate_items(()).free_items() {
        if let DefKind::Struct | DefKind::Enum = tcx.def_kind(item.owner_id) {
            for variant in tcx.adt_def(item.owner_id).variants() {
                if let Some((CtorKind::Fn, ctor_def_id)) = variant.ctor {
                    set.insert(ctor_def_id.expect_local());
                }
            }
        }
    }

    // Trust (I5, wiring site 3): Clean-origin defs have MIR but are not HIR body
    // owners, so the seed above cannot see them and no later loop reaches them
    // either — a tuple ctor is found through `hir_crate_items`, which is also
    // HIR. Without this insertion the body would never be demanded, never
    // encoded in metadata, and never `--emit=mir` visible: the def would exist,
    // resolve, and type-check, and then quietly have no code.
    //
    // This iterates the Clean-origin REGISTRY, not a filter over some other
    // enumeration. That distinction is load-bearing and was got wrong once
    // already: every `tcx`-side inventory of definitions available here —
    // `hir_body_owners`, `hir_crate_items(()).definitions()`,
    // `hir_crate_items(()).free_items()` — is derived from HIR, and a
    // Clean-origin def is precisely the thing that has none. A predicate
    // applied to any of them would be vacuously false forever and the omission
    // would look like a working filter.
    set.extend(clean_origin_mir::clean_origin_defs(tcx));

    set
}

fn mir_const_qualif(tcx: TyCtxt<'_>, def: LocalDefId) -> ConstQualifs {
    // Avoid the `mir_built` call for trivial consts.
    if let Some((_val, ty)) = tcx.trivial_const(def) {
        let has_mut_interior = !ty.is_trivially_freeze();
        let needs_drop =
            ty.needs_drop(tcx, TypingEnv::post_typeck_through_borrowck_for_mir_build(tcx, def));

        // These will only fail if the set of things accepted by `trivial_const` expands.
        assert!(!has_mut_interior);
        assert!(!needs_drop);

        return ConstQualifs {
            has_mut_interior,
            needs_drop,
            needs_non_const_drop: needs_drop,
            tainted_by_errors: None,
        };
    }

    // N.B., this `borrow()` is guaranteed to be valid (i.e., the value
    // cannot yet be stolen), because `mir_promoted()`, which steals
    // from `mir_built()`, forces this query to execute before
    // performing the steal.
    let body = &tcx.mir_built(def).borrow();
    let ccx = check_consts::ConstCx::new(tcx, body);
    // No need to const-check a non-const `fn`.
    match ccx.const_kind {
        Some(ConstContext::Const { .. } | ConstContext::Static(_) | ConstContext::ConstFn) => {}
        None => span_bug!(
            tcx.def_span(def),
            "`mir_const_qualif` should only be called on const fns and const items"
        ),
    }

    if body.return_ty().references_error() {
        // It's possible to reach here without an error being emitted (#121103).
        tcx.dcx().span_delayed_bug(body.span, "mir_const_qualif: MIR had errors");
        return Default::default();
    }

    let mut validator = check_consts::check::Checker::new(&ccx);
    validator.check_body();

    // We return the qualifs in the return place for every MIR body, even though it is only used
    // when deciding to promote a reference to a `const` for now.
    validator.qualifs_in_return_place()
}

/// Implementation of the `mir_built` query.
fn mir_built(tcx: TyCtxt<'_>, def: LocalDefId) -> &Steal<Body<'_>> {
    // Delegate to the main MIR building code in the `rustc_mir_build` crate.
    // This is the one place that is allowed to call `build_mir_inner_impl`.
    let mut body = tcx.build_mir_inner_impl(def);

    // Trust (effect conservation, 2026-10-01): the MIR ORACLE's effect census — calls, stores
    // through escaping pointers, drops, asm — of exactly the body the `-Ztrust-ir-lower` hook
    // inside `build_mir_inner_impl` just compared its trust-ir against, before any pass below
    // touches it. Read-only; a no-op unless the trust-ir producer lane runs. Here and not in the
    // hook because the hook's file is frozen; see `trust_thir_lower::effect_conservation`.
    trust_thir_lower::effect_conservation::record_mir_census(tcx, def, &body);

    pass_manager::dump_mir_for_phase_change(tcx, &body);

    // Skip all the passes below for trivial consts.
    if tcx.trivial_const(def).is_none() {
        pm::run_passes(
            tcx,
            &mut body,
            &[
                // This used to be part of MIR building,
                // now done separately to separate concerns.
                &lint_and_remove_uninhabited::LintAndRemoveUninhabited,
                // MIR-level lints.
                &Lint(check_inline::CheckForceInline),
                &Lint(check_call_recursion::CheckCallRecursion),
                &Lint(check_packed_ref::CheckPackedRef),
                &Lint(check_const_item_mutation::CheckConstItemMutation),
                &Lint(check_mut_restriction::CheckMutRestriction),
                &Lint(function_item_references::FunctionItemReferences),
                // What we need to do constant evaluation.
                &simplify::SimplifyCfg::Initial,
                &Lint(sanity_check::SanityCheck),
            ],
            None,
        );
    }
    tcx.alloc_steal_mir(body)
}

/// Compute the main MIR body and the list of MIR bodies of the promoteds.
fn mir_promoted(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
) -> (&Steal<Body<'_>>, &Steal<IndexVec<Promoted, Body<'_>>>) {
    debug_assert!(!tcx.is_trivial_const(def), "Tried to get mir_promoted of a trivial const");
    debug_assert!(!tcx.is_constructor(def.to_def_id()));

    // Ensure that we compute the `mir_const_qualif` for constants at
    // this point, before we steal the mir-const result.
    // Also this means promotion can rely on all const checks having been done.

    let const_qualifs = match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
            if matches!(tcx.constness(def), hir::Constness::Const { .. }) =>
        {
            tcx.mir_const_qualif(def)
        }
        DefKind::AssocConst | DefKind::Const | DefKind::Static { .. } | DefKind::AnonConst => {
            tcx.mir_const_qualif(def)
        }
        _ => ConstQualifs::default(),
    };

    // the `has_ffi_unwind_calls` query uses the raw mir, so make sure it is run.
    tcx.ensure_done().has_ffi_unwind_calls(def);

    // the `by_move_body` query uses the raw mir, so make sure it is run.
    if tcx.needs_coroutine_by_move_body_def_id(def.to_def_id()) {
        tcx.ensure_done().coroutine_by_move_body_def_id(def);
    }

    // Retain actual Clean references before raw MIR is consumed. A query result,
    // rather than a provider side effect, also survives incremental replay and
    // captures bodies fed by coroutine/custom-MIR paths. Ordinary Rust crates
    // with no minted Clean definitions need no additional per-body query.
    if !tcx.resolutions(()).clean_origin_defs.is_empty() {
        tcx.ensure_done().trust_clean_origin_references(def);
    }

    let mut body = tcx.mir_built(def).steal();
    if let Some(error_reported) = const_qualifs.tainted_by_errors {
        body.tainted_by_errors = Some(error_reported);
    }

    // Collect `required_consts` *before* promotion, so if there are any consts being promoted
    // we still add them to the list in the outer MIR body.
    RequiredConstsVisitor::compute_required_consts(&mut body);

    // What we need to run borrowck etc.
    let promote_pass = promote_consts::PromoteTemps::default();
    pm::run_passes(
        tcx,
        &mut body,
        &[&promote_pass, &simplify::SimplifyCfg::PromoteConsts, &coverage::InstrumentCoverage],
        Some(MirPhase::Analysis(AnalysisPhase::Initial)),
    );

    // Avoid over-capacity in the vectors of basic blocks, which can take up substantial memory.
    // This costs a tiny bit of performance to save a lot of memory.
    for bb in body.basic_blocks.as_mut_preserves_cfg() {
        bb.statements.shrink_to_fit();
    }

    lint_tail_expr_drop_order::run_lint(tcx, def, &body);

    let promoted = promote_pass.promoted_fragments.into_inner();
    (tcx.alloc_steal_mir(body), tcx.alloc_steal_promoted(promoted))
}

/// Compute the MIR that is used during CTFE (and thus has no optimizations run on it)
fn mir_for_ctfe(tcx: TyCtxt<'_>, def_id: LocalDefId) -> &Body<'_> {
    debug_assert!(!tcx.is_trivial_const(def_id), "Tried to get mir_for_ctfe of a trivial const");
    tcx.arena.alloc(inner_mir_for_ctfe(tcx, def_id))
}

/// Preserve elaborated MIR for query-cycle-safe Trust verification after `optimized_mir`
/// consumes the source [`Steal`].
///
/// `None` when the source was already stolen. The pre-steal snapshot in
/// [`inner_optimized_mir`] guarantees `Some` for mutual-recursion SCC members —
/// but the CONSUMERS route through `optimized_mir_query_would_cycle`, which is
/// deliberately WIDER (it also covers live query ancestors outside any static
/// SCC), and that dynamic remainder cannot be snapshotted ahead of the steal.
/// Callers in that gap used to reach a post-steal `borrow()` and abort the
/// build with a `Steal` panic; they all sit inside fail-soft loops whose
/// designed degradation is the absent-callee may-panic marker, so `None` is the
/// contract they already honor.
fn mir_for_trust_verification(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<&Body<'_>> {
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    if body.is_stolen() {
        // The elaborated-MIR `Steal` was consumed by `optimized_mir`. If that query
        // (or an ancestor it transitively reaches) is still IN PROGRESS, re-entering
        // it here would cycle — honor the fail-soft `None` contract (callers degrade
        // via the absent-callee may-panic marker). Otherwise `optimized_mir` has
        // necessarily already COMPLETED and is CACHED (per-monomorphization callee
        // bundling can read `optimized_mir`/`instance_mir` for ONE instance of a
        // generic fn — stealing the SHARED elaborated body — and then need this
        // snapshot for the generic def or another instance), so fall back to its
        // further-optimized real-codegen body — a sound source for structural/
        // interprocedural verification. Prevents the `body.borrow()` ICE without
        // giving up coverage in the completed-and-cached case.
        if trust_verify::optimized_mir_query_would_cycle(tcx, def_id.to_def_id()) {
            return None;
        }
        return Some(tcx.optimized_mir(def_id));
    }
    Some(tcx.arena.alloc(body.borrow().clone()))
}

fn inner_mir_for_ctfe(tcx: TyCtxt<'_>, def: LocalDefId) -> Body<'_> {
    // Trust (I5, wiring site 4a): THE VERY TOP, and deliberately so.
    //
    // Before `is_constructor`, and — load-bearing — before
    // `hir_body_const_context` below, whose `None` arm is a hard
    // `bug!("mir_for_ctfe called on non-const")`. A Clean-origin def has no HIR,
    // so a const that calls one walks into that `bug!` unless the gate answers
    // first. `mir_for_ctfe` is also why the gate cannot live on the codegen arm
    // alone: a `const` never reaches `optimized_mir`, so a gate installed only
    // there is bypassed by every constant in the program while the value is
    // still baked into the binary.
    //
    // NOT behind `verification_enabled` and NOT behind `-Ztrust-verify=off`.
    // The faithfulness gate is a compilation-correctness check on emitted code,
    // not an obligation; a gate a flag can switch off is a lint.
    if let Some(body) = clean_origin_mir::clean_origin_mir(tcx, def) {
        // Trust (plan step 3.5, design §5.7): every build of a Clean-origin body is counted,
        // here by const evaluation's reader.
        clean_origin_ir::clean_origin_reach::hook_ran(tcx.sess, true);
        return body;
    }
    if tcx.is_constructor(def.to_def_id()) {
        // There's no reason to run all of the MIR passes on constructors when
        // we can just output the MIR we want directly. This also saves const
        // qualification and borrow checking the trouble of special casing
        // constructors.
        return shim::build_adt_ctor(tcx, def.to_def_id());
    }

    let body = tcx.mir_drops_elaborated_and_const_checked(def);
    let (body, always) = match tcx.hir_body_const_context(def) {
        // consts and statics do not have `optimized_mir`, so we can steal the body instead of
        // cloning it.
        Some(hir::ConstContext::Const { .. } | hir::ConstContext::Static(_)) => {
            (body.steal(), true)
        }
        Some(hir::ConstContext::ConstFn) => (body.borrow().clone(), false),
        None => bug!("`mir_for_ctfe` called on non-const {def:?}"),
    };

    let mut body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::Const { always });
    // Trust (CTFE flip lane): const/associated-const ITEMS whose THIR→trust-ir lowering was proven
    // DerivedAgreed at the `mir_built` hook now const-evaluate MIR RE-DERIVED FROM THE TRUST-IR
    // MODULE instead of the built body — the CTFE mirror of `inner_optimized_mir`'s flip. Const
    // qualification already ran on the built sibling (`mir_const_qualif` reads `mir_built`), so the
    // derived body inherits its verdict. Any gate/pipeline failure or
    // pass panic preserves the retained built body with a loud compatibility-fallback `warn!`;
    // that body does not count as direct-TrustIR coverage.
    // The passes below then run on the (derived or built) body identically. Escape:
    // `-Ztrust-ir-flip=no`.
    //
    // Trust: what this seam ADMITS is wider than the sentence above reads, and the difference is
    // not covered by a test — state it rather than let the next reader assume. The gate accepts
    // `ConstContext::Const { .. } | ConstContext::Static(_)` (`trust_ir_flip.rs:205`), so STATICS
    // are admitted, not gated out. And a `comptime` fn — `Constness::Const { always: true }` —
    // is mapped to `ConstContext::Const { .. }` by `hir::map`'s `hir_body_const_context`, so it
    // reaches this seam too, despite `try_flip_ctfe`'s own comment saying a const FN cannot.
    // That matters because of the phase argument below: the comptime-fn arm runs
    // `[CtfeLimit, MentionedItems]` with phase `None`, and `pass_manager`'s mandatory validation
    // fires only on a phase change to `Runtime(Optimized)`. So unlike the codegen seam, a
    // trust-ir-DERIVED body on this path is never validated before `instance_mir` serves it.
    // Not reachable from runtime code today, but only because typeck rejects runtime calls to
    // comptime fns — this gate does not close it. Excluding comptime fns here, or validating the
    // derived body, is a behaviour change on a proof-relevant seam and wants its own evidence.
    let mut derived_from_trust_ir = false;
    if let Some(flipped) = trust_ir_flip::try_flip_ctfe(tcx, def, &body) {
        body = flipped;
        derived_from_trust_ir = true;
    }
    // FIXME(reflection): probably need to look at this for comptime closures
    let passes: &[&dyn MirPass<'_>] = if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && matches!(tcx.constness(def), hir::Constness::Const { always: true })
    {
        // Need to generate mentioned items, as all functions are expected to have them, but for const
        // fns we just look at the optimized MIR, which generates it. For comptime fns, there is no
        // optimized MIR.
        &[&ctfe_limit::CtfeLimit, &mentioned_items::MentionedItems]
    } else {
        &[&ctfe_limit::CtfeLimit]
    };
    pm::run_passes(tcx, &mut body, passes, None);

    // Trust: validate a trust-ir-DERIVED body before serving it. The call above passes phase
    // `None`, and `pass_manager` makes validation mandatory only on a phase change to
    // `Runtime(Optimized)` — which this seam never performs. So unlike the codegen seam, where the
    // flipped body goes through `run_optimization_passes` and its Optimized-phase validation, a
    // derived body here reached `instance_mir`'s consumers entirely unvalidated. Only the derived
    // case is validated: the built body is already covered by the passes that produced it, and
    // validating it here would be a cost on every const-eval for no new information.
    if derived_from_trust_ir {
        pm::validate_body(tcx, &mut body, "after trust-ir CTFE flip".to_string());
    }

    body
}

/// Obtain just the main MIR (no promoteds) and run some cleanups on it. This also runs
/// mir borrowck *before* doing so in order to ensure that borrowck can be run and doesn't
/// end up missing the source MIR due to stealing happening.
fn mir_drops_elaborated_and_const_checked(tcx: TyCtxt<'_>, def: LocalDefId) -> &Steal<Body<'_>> {
    // Trust (I5, the ROOT fix for the mir_keys dead-end family): a Clean-origin
    // def has no ordinary MIR pipeline — the walk below (`mir_borrowck` ->
    // `mir_promoted` -> `mir_built` -> `check_match` -> `typeck`) dead-ends in
    // `typeck`, which `span_bug!`s on a def with a synthetic HIR owner and no
    // body. SIX separate consumers reached that dead-end one at a time (the
    // verify pass's backing inventory, the R1 call-graph scan, the MIR
    // pipeline, the R1 flip harvest, the coverage denominator, and the
    // mutual-recursion oracle's adjacency), each patched at the caller before
    // this seam was identified. Serving the query HERE makes it total over
    // `mir_keys`, so every present and future consumer reads the same thing:
    // the kernel-gated emission, which IS this def's body.
    //
    // `optimized_mir` is the cached authority for that emission (the gate runs
    // once per def there); this clone is a handful of statements. The phase is
    // `Runtime(Optimized)` — ahead of what this query normally carries — which
    // is sound for every reader (they extract facts; none replays the
    // analysis-to-runtime pipeline on it, and the ordinary pipeline that WOULD
    // is bypassed for Clean-origin defs at `inner_optimized_mir`'s own early
    // return). No cycle: the emission never reads this query.
    if clean_origin_mir::is_clean_origin(tcx, def) {
        return tcx.alloc_steal_mir(tcx.optimized_mir(def.to_def_id()).clone());
    }
    if tcx.is_coroutine(def.to_def_id()) {
        tcx.ensure_done().mir_coroutine_witnesses(def);
    }

    // We only need to borrowck non-synthetic MIR.
    let tainted_by_errors = if !tcx.is_synthetic_mir(def) {
        tcx.mir_borrowck(tcx.typeck_root_def_id_local(def)).err()
    } else {
        None
    };

    let is_fn_like = tcx.def_kind(def).is_fn_like();
    if is_fn_like {
        // Do not compute the mir call graph without said call graph actually being used.
        if pm::should_run_pass(&inline::Inline, &pm::PassCtx::for_body(tcx, def.to_def_id()))
            || inline::ForceInline::should_run_pass_for_callee(tcx, def.to_def_id())
        {
            tcx.ensure_done().mir_inliner_callees(ty::InstanceKind::Item(def.to_def_id()));
        }
    }

    tcx.ensure_done().check_liveness(def);

    let (body, _) = tcx.mir_promoted(def);
    let mut body = body.steal();

    if let Some(error_reported) = tainted_by_errors {
        body.tainted_by_errors = Some(error_reported);
    }

    let root = tcx.typeck_root_def_id_local(def);
    if !tcx.is_synthetic_mir(root)
        && let Err(e) = tcx.check_transmutes(root)
    {
        body.tainted_by_errors = Some(e);
    }

    // Also taint the body if it's within a top-level item that is not well formed.
    //
    // We do this check here and not during `mir_promoted` because that may result
    // in borrowck cycles if WF requires looking into an opaque hidden type.
    match tcx.def_kind(root) {
        DefKind::Fn
        | DefKind::AssocFn
        | DefKind::Static { .. }
        | DefKind::Const
        | DefKind::AssocConst => {
            if let Err(guar) = tcx.ensure_result().check_well_formed(root) {
                body.tainted_by_errors = Some(guar);
            }
        }
        _ => {}
    }

    run_analysis_to_runtime_passes(tcx, &mut body);

    tcx.alloc_steal_mir(body)
}

// Made public so that `mir_drops_elaborated_and_const_checked` can be overridden
// by custom rustc drivers, running all the steps by themselves. See #114628.
pub fn run_analysis_to_runtime_passes<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    assert!(body.phase == MirPhase::Analysis(AnalysisPhase::Initial));
    let did = body.source.def_id();

    debug!("analysis_mir_cleanup({:?})", did);
    run_analysis_cleanup_passes(tcx, body);
    assert!(body.phase == MirPhase::Analysis(AnalysisPhase::PostCleanup));

    // Do a little drop elaboration before const-checking if `const_precise_live_drops` is enabled.
    if (tcx.features().const_precise_live_drops()
        || tcx.features().staged_api()
        || tcx.sess.opts.unstable_opts.force_unstable_if_unmarked)
        && check_consts::post_drop_elaboration::checking_enabled(&ConstCx::new(tcx, body))
    {
        pm::run_passes(
            tcx,
            body,
            &[
                &remove_uninit_drops::RemoveUninitDrops,
                &simplify::SimplifyCfg::RemoveFalseEdges,
                &Lint(post_drop_elaboration::CheckLiveDrops),
            ],
            None,
        );
    }

    debug!("runtime_mir_lowering({:?})", did);
    run_runtime_lowering_passes(tcx, body);
    assert!(body.phase == MirPhase::Runtime(RuntimePhase::Initial));

    debug!("runtime_mir_cleanup({:?})", did);
    run_runtime_cleanup_passes(tcx, body);
    assert!(body.phase == MirPhase::Runtime(RuntimePhase::PostCleanup));
}

// FIXME(JakobDegen): Can we make these lists of passes consts?

/// After this series of passes, no lifetime analysis based on borrowing can be done.
fn run_analysis_cleanup_passes<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let passes: &[&dyn MirPass<'tcx>] = &[
        &impossible_clauses::ImpossibleClauses,
        &cleanup_post_borrowck::CleanupPostBorrowck,
        &remove_noop_landing_pads::RemoveNoopLandingPads,
        &simplify::SimplifyCfg::PostAnalysis,
        &deref_separator::Derefer,
    ];

    pm::run_passes(tcx, body, passes, Some(MirPhase::Analysis(AnalysisPhase::PostCleanup)));
}

/// Returns the sequence of passes that lowers analysis to runtime MIR.
fn run_runtime_lowering_passes<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let passes: &[&dyn MirPass<'tcx>] = &[
        // These next passes must be executed together.
        &add_call_guards::CriticalCallEdges,
        // Must be done before drop elaboration because we need to drop opaque types, too.
        &post_analysis_normalize::PostAnalysisNormalize,
        // Calling this after `PostAnalysisNormalize` ensures that we don't deal with opaque types.
        &add_subtyping_projections::Subtyper,
        &elaborate_drops::ElaborateDrops,
        // Needs to happen after drop elaboration.
        &Lint(check_call_recursion::CheckDropRecursion),
        // This will remove extraneous landing pads which are no longer
        // necessary as well as forcing any call in a non-unwinding
        // function calling a possibly-unwinding function to abort the process.
        &abort_unwinding_calls::AbortUnwindingCalls,
        // AddMovesForPackedDrops needs to run after drop
        // elaboration.
        &add_moves_for_packed_drops::AddMovesForPackedDrops,
        &erase_deref_temps::EraseDerefTemps,
        &elaborate_box_derefs::ElaborateBoxDerefs,
        &coroutine::StateTransform,
        &Lint(known_panics_lint::KnownPanicsLint),
    ];
    pm::run_passes_no_validate(tcx, body, passes, Some(MirPhase::Runtime(RuntimePhase::Initial)));
}

/// Returns the sequence of passes that do the initial cleanup of runtime MIR.
fn run_runtime_cleanup_passes<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let passes: &[&dyn MirPass<'tcx>] = &[
        &lower_intrinsics::LowerIntrinsics,
        &remove_place_mention::RemovePlaceMention,
        &simplify::SimplifyCfg::PreOptimizations,
    ];

    pm::run_passes(tcx, body, passes, Some(MirPhase::Runtime(RuntimePhase::PostCleanup)));

    // Clear diagnostic binding data by anticipation. A body with first-class
    // Trust loop contracts is the one exception: certified runtime monitor
    // placement needs a compact compiler-owned binding identity after
    // `var_debug_info` has been omitted or stripped. Preserve only that HIR
    // identity; all diagnostic-only VarBindingForm fields are still discarded.
    let retain_trust_source_bindings = body.source.promoted.is_none()
        && body
            .source
            .def_id()
            .as_local()
            .and_then(|local| tcx.hir_maybe_body_owned_by(local))
            .and_then(|body| body.contract)
            .is_some_and(|contract| !contract.loop_clauses.is_empty());
    if !retain_trust_source_bindings {
        for decl in &mut body.local_decls {
            decl.local_info = ClearCrossCrate::Clear;
        }
        return;
    }
    for decl in &mut body.local_decls {
        if let ClearCrossCrate::Set(info) = &decl.local_info {
            match &**info {
                LocalInfo::User(BindingForm::Var(binding)) => {
                    let hir_local_id = binding.binding_hir_local_id.as_u32();
                    decl.local_info =
                        ClearCrossCrate::Set(Box::new(LocalInfo::TrustSourceBinding {
                            hir_local_id,
                        }));
                    continue;
                }
                // A TrustIR-flipped body is reconstructed at `Built` with
                // this compact carrier already authenticated from the
                // module's sealed source-place provenance. Advancing that
                // body through the ordinary cleanup pipeline must retain
                // the carrier just as it retains one derived from native
                // MIR; clearing it here silently disables E4/E5 monitors
                // only on the default flipped codegen path.
                LocalInfo::TrustSourceBinding { .. } => continue,
                _ => {}
            }
        }
        decl.local_info = ClearCrossCrate::Clear;
    }
}

pub(crate) fn run_optimization_passes<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // Trust: the pipeline lives in `run_optimization_pipeline`, which can also run it
    // without its final `TrustVerify` pass (`trust_once_coroutine_mir`).
    run_optimization_pipeline(tcx, body, true)
}

// Trust: `with_trust_verify: false` omits exactly the final `TrustVerify` pass and
// nothing else — the pipeline the vanilla (`-Ztrust-verify=off`) lane runs, where that
// pass is disabled.
fn run_optimization_pipeline<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    with_trust_verify: bool,
) {
    fn o1<T>(x: T) -> WithMinOptLevel<T> {
        WithMinOptLevel(1, x)
    }

    // The main optimizations that we do on MIR.
    pm::run_passes(
        tcx,
        body,
        &[
            // Add some UB checks before any UB gets optimized away.
            // Trust: the spawn census runs these three on its copy of each local body
            // (`trust_spawn_census_ub_checks`): keep the two lists the same.
            &check_alignment::CheckAlignment,
            &check_null::CheckNull,
            &check_enums::CheckEnums,
            // Before inlining: trim down MIR with passes to reduce inlining work.

            // Has to be done before inlining, otherwise actual call will be almost always inlined.
            // Also simple, so can just do first.
            &lower_slice_len::LowerSliceLenCalls,
            // Perform instsimplify before inline to eliminate some trivial calls (like clone
            // shims).
            &instsimplify::InstSimplify::BeforeInline,
            // Perform inlining of `#[rustc_force_inline]`-annotated callees.
            &inline::ForceInline,
            // Perform inlining, which may add a lot of code.
            &inline::Inline,
            // Inlining may have introduced a lot of redundant code and a large move pattern.
            // Now, we need to shrink the generated MIR.
            // Code from other crates may have storage markers, so this needs to happen after
            // inlining.
            &remove_storage_markers::RemoveStorageMarkers,
            // Inlining and instantiation may introduce ZST and useless drops.
            &remove_zsts::RemoveZsts,
            &remove_unneeded_drops::RemoveUnneededDrops,
            // Type instantiation may create uninhabited enums.
            // Also eliminates some unreachable branches based on variants of enums.
            &unreachable_enum_branching::UnreachableEnumBranching,
            &unreachable_prop::UnreachablePropagation,
            &o1(simplify::SimplifyCfg::AfterUnreachableEnumBranching),
            &multiple_return_terminators::MultipleReturnTerminators,
            // After simplifycfg, it allows us to discover new opportunities for peephole
            // optimizations. This invalidates CFG caches, so avoid putting between
            // `ReferencePropagation` and `GVN` which both use the dominator tree.
            &instsimplify::InstSimplify::AfterSimplifyCfg,
            // After `InstSimplify-after-simplifycfg` with `-Zub_checks=false`, simplify
            // ```
            // _13 = const false;
            // assume(copy _13);
            // Call(precondition_check);
            // ```
            // to unreachable to eliminate the call to help later passes.
            // This invalidates CFG caches also.
            &o1(simplify_branches::SimplifyConstCondition::AfterInstSimplify),
            &ref_prop::ReferencePropagation,
            &sroa::ScalarReplacementOfAggregates,
            &simplify::SimplifyLocals::BeforeConstProp,
            &dead_store_elimination::DeadStoreElimination::Initial,
            &gvn::GVN,
            // Trust: rust-lang#127553 — after GVN has merged identical index/length
            // computations into the same SSA local, drop asserts (in particular
            // BoundsCheck) that are dominated by an identical assert. Runs before
            // SimplifyLocals so the dead condition locals get cleaned up.
            &redundant_bounds_check::RedundantBoundsCheckElim,
            &simplify::SimplifyLocals::AfterGVN,
            // This pass does attempt to track assignments.
            // Keep it close to GVN which merges identical values into the same local.
            &ssa_range_prop::SsaRangePropagation,
            &match_branches::MatchBranchSimplification,
            &dataflow_const_prop::DataflowConstProp,
            &single_use_consts::SingleUseConsts,
            &o1(simplify_branches::SimplifyConstCondition::AfterConstProp),
            &jump_threading::JumpThreading,
            &early_otherwise_branch::EarlyOtherwiseBranch,
            &simplify_comparison_integral::SimplifyComparisonIntegral,
            &o1(simplify_branches::SimplifyConstCondition::Final),
            &o1(remove_noop_landing_pads::RemoveNoopLandingPads),
            &o1(simplify::SimplifyCfg::Final),
            // After the last SimplifyCfg, because this wants one-block functions.
            &strip_debuginfo::StripDebugInfo,
            &copy_prop::CopyProp,
            &dead_store_elimination::DeadStoreElimination::Final,
            &dest_prop::DestinationPropagation,
            &tail_copy_to_move::TailCopyToMove,
            &move_elimination::MoveElimination,
            &simplify::SimplifyLocals::Final,
            &multiple_return_terminators::MultipleReturnTerminators,
            // Some cleanup necessary at least for LLVM and potentially other codegen backends.
            &add_call_guards::CriticalCallEdges,
            // Cleanup for human readability, off by default.
            &prettify::ReorderBasicBlocks,
            &prettify::ReorderLocals,
            // Trust: verify the fully optimized MIR just before codegen — or, for the
            // vanilla pipeline, run nothing in its place (`TrustVerifyWhen`).
            &TrustVerifyWhen(with_trust_verify),
        ],
        Some(MirPhase::Runtime(RuntimePhase::Optimized)),
    );
}

// Trust (spawn census, design 2026-09-29-spawn-census-by-construction §5.2): the
// UB-check passes that open `run_optimization_pipeline`, run on the census's copy of a
// pre-steal local body. They add panics (a misaligned or null pointer dereference, an
// invalid enum construction) after the body the census reads; without them the census
// saw no edge to those panics, and a spawning panic hook made the panic a QUIET spawn.
// Each runs exactly when the pipeline would run it (`should_run_pass`: `-Zub-checks`,
// `-Zmir-enable-passes`).
pub(crate) fn trust_spawn_census_ub_checks<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let ctx = pm::PassCtx::for_body(tcx, body.source.def_id());
    for pass in trust_spawn_census_ub_check_passes() {
        if pm::should_run_pass(pass, &ctx) {
            pass.run_pass(tcx, body);
        }
    }
}

// Trust (spawn census P4): whether any of those UB checks runs in this compilation, for the
// census's trust-ir shadow lane, which reads no MIR and charges a body that may need one.
pub(crate) fn trust_spawn_census_ub_checks_run(tcx: TyCtxt<'_>) -> bool {
    // The three passes' policies read only the session (`ub_checks`), so the
    // crate root stands in for a body when building the pass context.
    let ctx = pm::PassCtx::for_body(tcx, rustc_hir::def_id::CRATE_DEF_ID.to_def_id());
    trust_spawn_census_ub_check_passes().into_iter().any(|pass| pm::should_run_pass(pass, &ctx))
}

fn trust_spawn_census_ub_check_passes<'a, 'tcx>() -> [&'a (dyn MirPass<'tcx> + 'a); 3] {
    [&check_alignment::CheckAlignment, &check_null::CheckNull, &check_enums::CheckEnums]
}

// Trust: the final pass of `run_optimization_pipeline`. `TrustVerifyWhen(true)` IS
// `TrustVerify` (every `MirPass` method forwards). `TrustVerifyWhen(false)` is the pass
// as the vanilla lane has it — disabled — and runs nothing even when
// `-Zmir-enable-passes=+TrustVerify` forces it on. Structural on purpose: a query this
// pipeline demands (e.g. a `#[rustc_force_inline]` callee's `optimized_mir`) runs its
// own pipeline with `TrustVerifyWhen(true)`, so no ambient "verification off" state
// can leak into a body that is really codegened.
struct TrustVerifyWhen(bool);

impl<'tcx> MirPass<'tcx> for TrustVerifyWhen {
    fn name(&self) -> &'static str {
        MirPass::name(&trust_verify::TrustVerify)
    }

    fn profiler_name(&self) -> &'static str {
        MirPass::profiler_name(&trust_verify::TrustVerify)
    }

    fn policy(&self, ctx: &PassCtx<'_>) -> PassPolicy {
        MirPass::policy(&trust_verify::TrustVerify, ctx)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if self.0 {
            MirPass::run_pass(&trust_verify::TrustVerify, tcx, body)
        }
    }

    fn is_mir_dump_enabled(&self) -> bool {
        MirPass::is_mir_dump_enabled(&trust_verify::TrustVerify)
    }
}

/// Optimize the MIR and prepare it for codegen.
fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    // Trust (I5, wiring site 4b): THE VERY TOP of the codegen arm.
    //
    // Placed in the OUTER function rather than in `inner_optimized_mir` because
    // `is_constructor` is tested here, and `is_constructor` reaches
    // `def_kind`/HIR-derived state for a def that has neither. Same rules as
    // the CTFE arm: sole constructor, fail-closed, and no verification switch
    // disables it.
    //
    // The body is returned WITHOUT `run_optimization_passes`. That is not an
    // omission: the gate's subject is the body this function returns, so a pass
    // that rewrote it after the gate ran would put un-gated code in the binary.
    // A widening that wants optimization must re-gate after it, not before.
    if let Some(body) = clean_origin_mir::clean_origin_mir(tcx, did) {
        // Trust (plan step 3.5, design §5.7): every build of a Clean-origin body is counted, for
        // the lane whose scope is open (`clean_origin_reach`).
        clean_origin_ir::clean_origin_reach::hook_ran(tcx.sess, false);
        return tcx.arena.alloc(body);
    }
    if tcx.is_constructor(did.to_def_id()) {
        // There's no reason to run all of the MIR passes on constructors when
        // we can just output the MIR we want directly. This also saves const
        // qualification and borrow checking the trouble of special casing
        // constructors.
        return tcx.mir_for_ctfe(did);
    }

    tcx.arena.alloc(inner_optimized_mir(tcx, did))
}

fn inner_optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> Body<'_> {
    match tcx.hir_body_const_context(did) {
        // Run the `mir_for_ctfe` query, which depends on `mir_drops_elaborated_and_const_checked`
        // which we are going to steal below. Thus we need to run `mir_for_ctfe` first, so it
        // computes and caches its result.
        Some(hir::ConstContext::ConstFn) => tcx.ensure_done().mir_for_ctfe(did),
        None => {}
        Some(other) => panic!("do not use `optimized_mir` for constants: {other:?}"),
    }
    // Trust: with verification enabled, a coroutine's layout is served from its pre-steal
    // elaborated MIR (`trust_local_coroutine_layout`, read by `ordinary_coroutine_layout`),
    // so it must be produced BEFORE the steal below. This must be a value-producing query
    // call, not `ensure_done`: on an incremental green replay an ensure-only call may mark
    // the dep-node green without caching its value, and a later `layout_of` would then
    // borrow the stolen body (same reason as `mir_for_trust_verification` below).
    let trust_coroutine_layout =
        if tcx.sess.trust_reads_pre_steal_mir() && tcx.is_coroutine(did.to_def_id()) {
            Some(tcx.trust_local_coroutine_layout(did))
        } else {
            None
        };
    debug!("about to call mir_drops_elaborated...");
    let elaborated = tcx.mir_drops_elaborated_and_const_checked(did);
    // Trust: the Clean-origin purity guard, which runs inside `mir_for_ctfe`, reads a
    // body of this crate through `trust_rust_purity_fact`, a fact of the pre-steal
    // elaborated MIR, so it must be produced BEFORE the steal below. Value-producing, not
    // `ensure_done`, for the incremental reason given for the coroutine layout above.
    if clean_origin_mir::crate_needs_purity_facts(tcx) {
        let _ = tcx.trust_rust_purity_fact(did);
    }
    // Trust verification needs an immutable elaborated-MIR fallback only for a
    // function in a mutual-recursion SCC. The compact, disk-cached adjacency
    // query proves that property before the source `Steal` is consumed. This
    // avoids cloning and retaining a second full Body for every ordinary
    // function while keeping recursive inspection query-order-independent.
    //
    // Trust (2026-09-29): the crate-wide SCC set (and the spawn census below) is
    // forced at the analysis seam (`trust_force_crate_graph_oracles`), before any
    // body is stolen and outside every type-system query; these two forces are the
    // idempotent fallback for a driver that never reaches that seam. With
    // verification enabled no type-system query reaches a local `optimized_mir`
    // any more (`trust_local_coroutine_layout`), so neither can run from inside
    // type computation.
    if trust_verify::verification_enabled(tcx.sess)
        && trust_verify::trust_mir_is_mutually_recursive(tcx, did)
    {
        // This must be a value-producing query call, not `ensure_done`: on an
        // incremental green replay an ensure-only call may skip this non-disk-
        // cached provider, leaving no in-memory snapshot.
        let _ = tcx.mir_for_trust_verification(did);
    }
    // Trust (spawn census): force the crate's spawn census while every local body's
    // elaborated MIR (THIS body's included) is still unstolen: its MIR adapter borrows
    // that MIR unguarded under the same contract as the SCC adjacency forced just above.
    // The placement of record is the analysis seam (`trust_force_crate_graph_oracles`);
    // forcing here too — before this body's `steal` — keeps that borrow legal for a
    // driver that skips the seam.
    if tcx.sess.trust_runs_spawn_census() {
        let _ = tcx.trust_spawn_census(());
    }
    let body = elaborated.steal();
    let mut body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst);

    if body.tainted_by_errors.is_some() {
        // Trust (assertion-grade coverage): an attributable pre-pass early-out — the
        // body carries an `ErrorGuaranteed` (the build already fails), so credit it
        // as processed instead of tripping the crate coverage assertion.
        trust_verify::trust_note_coverage_early_out(
            tcx,
            did,
            trust_verify::CoverageEarlyOutKind::TaintedByErrors,
        );
        return body;
    }

    // Trust: P1 item 5 — the trust-ir flip. If this body's THIR→trust-ir lowering was proven
    // equivalent to the built MIR at the `mir_built` hook (`DerivedAgreed`), consume MIR
    // re-derived from the trust-ir Module on the codegen path (`-Z trust-ir-lower`;
    // `-Ztrust-ir-flip=no` escape hatch). Borrowck, CTFE (`mir_for_ctfe`, ensured above) and
    // `promoted_mir` stay on the built MIR. Any gate/pipeline failure preserves `body`, loudly,
    // as a compatibility fallback; it does not count as direct-TrustIR coverage. See
    // trust_ir_flip.rs.
    if let Some(flipped) = trust_ir_flip::try_flip(tcx, did, &body) {
        body = flipped;
    }

    // Before doing anything, remember which items are being mentioned so that the set of items
    // visited does not depend on the optimization level.
    // We do not use `run_passes` for this as that might skip the pass if `injection_phase` is set.
    mentioned_items::MentionedItems.run_pass(tcx, &mut body);

    // If `mir_drops_elaborated_and_const_checked` found that the current body has unsatisfiable
    // predicates, it will shrink the MIR to a single `unreachable` terminator.
    // More generally, if MIR is a lone `unreachable`, there is nothing to optimize.
    if let TerminatorKind::Unreachable = body.basic_blocks[START_BLOCK].terminator().kind
        && body.basic_blocks[START_BLOCK].statements.is_empty()
    {
        // Trust (assertion-grade coverage): a lone-`unreachable` body has no
        // executable path — verification coverage is vacuous (and it contributes no
        // obligation rows, so this credit can never mint proof). Credit it as
        // processed so a legitimately-green crate containing one does not
        // false-alarm the coverage assertion.
        trust_verify::trust_note_coverage_early_out(
            tcx,
            did,
            trust_verify::CoverageEarlyOutKind::VacuouslyUnreachable,
        );
        return body;
    }

    run_optimization_passes(tcx, &mut body);

    // Trust: the layout `ordinary_coroutine_layout` served from the pre-steal elaborated
    // MIR must be the layout of the body that is codegened. `StateTransform` is its only
    // writer and no optimization pass (TrustVerify's elision and monitor injection
    // included) touches `body.coroutine`, so a mismatch is a compiler bug — an ICE, never
    // a silent disagreement between a type's layout and its resume function.
    if let Some(pre_steal) = trust_coroutine_layout
        && body.coroutine_layout_raw() != pre_steal
    {
        bug!(
            "Trust: coroutine `{}` changed its layout after `trust_local_coroutine_layout` \
             read it from elaborated MIR",
            tcx.def_path_str(did)
        );
    }

    body
}

// Trust: provider of `trust_once_coroutine_mir` (see its doc in `rustc_middle`) — the
// coroutine body the vanilla lane's `optimized_mir` produces at this session's MIR opt
// level (which, at `-O`, is lower in a verifying session: ruling R1), computed from a
// CLONE of the elaborated MIR so nothing is stolen. The steps are `inner_optimized_mir`'s after its
// steal, in order, minus what cannot apply: the trust-ir flip refuses coroutines, and
// the coverage credits and the layout-parity check belong to the codegened body.
// `is_stolen` only picks between two views of the same coroutine (both vanilla-optimized
// but for TrustVerify's instrumentation), and the query is neither hashed nor disk-cached.
#[allow(rustc::untracked_query_information)]
fn trust_once_coroutine_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    let elaborated = tcx.mir_drops_elaborated_and_const_checked(did);
    if elaborated.is_stolen() {
        // Some other route already optimized this coroutine; read that body (a cache hit:
        // the steal is the proof that `optimized_mir` ran). With verification enabled
        // nothing on the ordinary pipeline steals a coroutine before the once-initializer
        // check (see `trust_local_coroutine_layout`); the once check is a deadlock
        // detector, never a premise, so this view only has to be the best available.
        return tcx.optimized_mir(did);
    }
    let body = elaborated.borrow().clone();
    let mut body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst);
    if body.tainted_by_errors.is_some() {
        return tcx.arena.alloc(body);
    }
    mentioned_items::MentionedItems.run_pass(tcx, &mut body);
    if let TerminatorKind::Unreachable = body.basic_blocks[START_BLOCK].terminator().kind
        && body.basic_blocks[START_BLOCK].statements.is_empty()
    {
        return tcx.arena.alloc(body);
    }
    run_optimization_pipeline(tcx, &mut body, false);
    tcx.arena.alloc(body)
}

/// Fetch all the promoteds of an item and prepare their MIR bodies to be ready for
/// constant evaluation once all generic parameters become known.
fn promoted_mir(tcx: TyCtxt<'_>, def: LocalDefId) -> &IndexVec<Promoted, Body<'_>> {
    // Trust (I5, wiring site 4c): the arm the plan did not name, and the one
    // that breaks first.
    //
    // The metadata encoder demands `promoted_mir` for every def in `mir_keys`,
    // and the ordinary path here reaches `mir_borrowck` -> `typeck` -> HIR. A
    // Clean-origin def has none of those. The early return mirrors the
    // constructor arm directly above: a projection body promotes nothing, so
    // the honest answer is an empty table, not a fabricated one.
    //
    // This does NOT re-run the gate, and must not: the promoted table is empty
    // by construction for the emitted shape, so there is nothing here for a
    // faithfulness verdict to be about. If a future shape can promote, its
    // promoteds are emitted code and need their own gate — do not widen this
    // early return to cover them.
    if clean_origin_mir::is_clean_origin(tcx, def) {
        return const { &IndexVec::new() };
    }
    if tcx.is_constructor(def.to_def_id()) {
        return const { &IndexVec::new() };
    }

    if !tcx.is_synthetic_mir(def) {
        tcx.ensure_done().mir_borrowck(tcx.typeck_root_def_id_local(def));
    }
    let mut promoted = tcx.mir_promoted(def).1.steal();
    if promoted.is_empty() {
        return const { &IndexVec::new() };
    }

    for body in &mut promoted {
        run_analysis_to_runtime_passes(tcx, body);
    }

    tcx.arena.alloc(promoted)
}

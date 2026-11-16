//! Trust (D8, 2026-09-24): the RETURNED-`Box` validity root.
//!
//! A `Box<T>` that reaches a caller as the whole destination of a call is a
//! valid value of its type — non-null, aligned for `T`, uniquely owning a live
//! allocation — WHEN the call is one whose result the Rust soundness contract
//! (and, for a callee in this crate, this crate's own verification) vouches
//! for. This module is the ONE predicate that decides which calls those are.
//! Both consumers read it, so they cannot drift apart:
//!
//!  * the extractor's `origin_of_box_local` (`convert.rs`), which discharges the
//!    compiler's `NullPointerDereference` / `MisalignedPointerDereference` MIR
//!    asserts on a deref of such a box ([`sole_call_def_is_returned_box_root`]);
//!  * trust-vcgen's separation engine (`sep_engine::box_value_is_validity_rooted`),
//!    which DROPS the `[unsafe:sep:*]` deref rows of such a box. vcgen holds no
//!    `TyCtxt`, so the compiler hands it the certified call BLOCKS
//!    ([`returned_box_root_call_blocks`]) through
//!    `VcgenContext::with_returned_box_root_blocks`, and vcgen additionally
//!    re-checks the call's own flags. Empty (every non-compiler caller) roots
//!    nothing.
//!
//! # What is admitted — every condition is load-bearing, and each rounds toward NO
//!
//! A `Call` terminator qualifies iff ALL of these hold:
//!
//! 0. the session runs no value-changing MIR optimization — no MIR inliner, no
//!    GVN, no `-Zmir-enable-passes=+..`. This is GUARANTEED, not checked here: a
//!    Trust proof session runs the `-O0` MIR pipeline at every `-Copt-level`
//!    (`rustc_session::trust_default_mir_opt_level_by_flags`) and refuses, by
//!    name, every option that would change which MIR passes run (T6,
//!    `rustc_driver_impl::trust_option_domain_error`), so the callee is
//!    verified on the very MIR it is compiled from. That refusal is this root's
//!    precondition: under the MIR inliner a sysroot `unsafe fn` inlined into the
//!    CALLEE loses its call-site row and GVN folds the value to a constant
//!    (MEASURED on the stage-1 `trustc` of 2026-09-24 at `-Copt-level=2
//!    -Zmir-opt-level=2`: `pub fn mk() -> Box<u32> { unsafe {
//!    transmute_neo::<usize, Box<u32>>(4) } }` verified, and only `count`'s own
//!    deref rows — the rows this root drops — refused `*mk()`). The check that
//!    stood here (`session_may_inline_or_fold_mir`) answered NO in every
//!    session that can reach this predicate once T6 refused those options, and
//!    was deleted with that refusal. `#[rustc_force_inline]` (the always-on
//!    `ForceInline` pass) is not covered: the sysroot carries no such function,
//!    and a user one is verified in its own right;
//! 1. its destination is a WHOLE local (no projection) whose type is
//!    `Box<T, Global>` (`is_box_global`: the `owned_box` lang item, which no
//!    crate can forge, with the `global_alloc_ty` lang item as its allocator —
//!    a user allocator's liveness is not the std premise);
//! 2. the callee operand is a DIRECT `FnDef` of a `fn` / associated `fn` whose
//!    generic arguments are fully concrete (modulo regions) — the same admission
//!    as `convert::callee_identity_for`, so it is exactly the set of calls vcgen
//!    sees with `callee_identity: Some(_)`. A `fn`-pointer / indirect call has
//!    no `FnDef` and is refused: a safe-typed pointer can be forged from an
//!    `unsafe fn` by a cast no row charges at the call;
//! 3. the called item's signature is SAFE outright (`Safety::Safe`; the
//!    `safe_target_features` carve-out `is_unsafe_sig` makes is NOT taken), its
//!    ABI is `Rust` / `rust-call`, and it is not a foreign item. An `unsafe fn`'s
//!    violated precondition makes the invalid box the caller's UB; a foreign
//!    item's safety claim (`unsafe extern { safe fn .. }`) is this crate's own
//!    undischarged declaration; a non-Rust ABI is an FFI boundary even when
//!    the body is Rust (a Rust-bodied `extern "C" fn` is refused);
//! 4. the call RESOLVES (`Instance::try_resolve` in the body's typing env) to
//!    `InstanceKind::Item` of a non-foreign `fn` / associated `fn` (safe, Rust
//!    ABI) or of a closure that is not a coroutine. A `dyn` method call
//!    resolves to `Virtual` and is refused here: it HAS a `callee_identity` (the
//!    arguments are concrete — `dyn Trait` is a concrete type), so without this
//!    arm the premise would silently cover every impl of the trait in the crate
//!    graph, verify-off dependencies included. Shims (`FnPtrShim`,
//!    `ClosureOnceShim`, `Intrinsic`, …) are refused for the same reason: the
//!    code that runs is not an item body anyone verified;
//! 5. neither the called item nor the resolved item (nor any ancestor, nor an
//!    impl's self type) carries a USER AXIOM — `#[trust::assume_total]` or
//!    `#[trust::skip]`. Those bodies are assumed, not verified, so "the callee's
//!    own verification discharges the premise" is false for them (D8 critique
//!    k4/k5);
//! 6. neither item has an EXTERN INDICATOR (`#[no_mangle]`, `#[export_name]`,
//!    `#[linkage]`, an externally implementable item, a std-internal symbol —
//!    `CodegenFnAttrs::contains_extern_indicator`), is `#[naked]`, or carries
//!    any `#[target_feature]` (for a closure, its enclosing `fn`'s too). An
//!    exported symbol can be interposed at link or load time, so the code that
//!    runs need not be the body that was verified; a naked body is assembly the
//!    verifier does not model; a target-feature body is UB to run on a CPU
//!    without the feature, so its result carries no guarantee there.
//!
//! Every exclusion is decided on a `DefId`, its resolved `Instance`, its
//! signature, its codegen attributes or its `trust::` tool attributes — never
//! on a rendered name.
//!
//! # Why this is not a false proof
//!
//! For a callee in THIS crate the premise is DISCHARGED: the callee's body is
//! verified, and every channel that can mint an invalid `Box` in a verified
//! body carries a refusing row — the D8-P0 creation row
//! `[unsafe:validity-transmute]` for a transmute (HIR and MIR), and the
//! existing unsafe-call / deref / union rows for `from_raw`, `ptr::read`,
//! `zeroed`, `assume_init`, `transmute_copy` (measured in the D8 memo). A local
//! body the verifier SKIPS is either a user axiom (conjunct 5), unreachable
//! from its entry (it never returns), or a memory-safe body whose skip is a
//! recorded assumption (`memory_safe_demotion_applies`: no source or inlined
//! `unsafe` at all, so every `Box` it returns came from a root or a charged
//! channel elsewhere); any other skip aborts the strict build. For a callee in
//! the sysroot or a verify-off dependency the premise is ASSUMED: a safe API
//! that returns an invalid `Box` is unsound, exactly as rustc's codegen already
//! assumes (`align`/`nonnull` return attributes). That is a TCB row
//! (docs/TCB.md, "Validity premises about values that arrive from outside the
//! checked body", the returned-`Box` row).
//!
//! The consumers' DATA-FLOW fences (single-valued local, no escaped address,
//! no partial write, no unmodeled write channel) are theirs, not this
//! module's: this predicate says only that the call's RESULT is valid.

use rustc_ast::attr::AttributeExt;
use rustc_hir::def::DefKind;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use trust_types::fx::FxHashSet;

/// The user axioms that make a body ASSUMED rather than verified.
const USER_AXIOM_ATTRS: &[&str] = &["assume_total", "skip"];

/// Is the `Call` `func(..) -> destination` a returned-`Box` validity root?
/// See the module doc for every condition and why each is required.
pub(crate) fn call_is_returned_box_validity_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    func: &mir::Operand<'tcx>,
    destination: mir::Place<'tcx>,
) -> bool {
    // (0) no value-changing MIR optimization in this session: guaranteed by
    // the proof session's refusal of every MIR-pipeline option (module doc).
    // (1) whole-local `Box<T, Global>` destination.
    if !destination.projection.is_empty()
        || !mir_body.local_decls[destination.local].ty.is_box_global(tcx)
    {
        return false;
    }
    // (2) direct, fully concrete `FnDef` of a `fn` / associated `fn`.
    let Some((called, args)) = func.const_fn_def() else { return false };
    if args.has_non_region_param()
        || args.has_non_region_infer()
        || args.has_non_region_placeholders()
    {
        return false;
    }
    if !matches!(tcx.def_kind(called), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    // (3) safe signature, Rust ABI, not foreign.
    if tcx.is_foreign_item(called) {
        return false;
    }
    let sig = tcx.fn_sig(called).skip_binder().skip_binder();
    if !sig_is_safe_rust_abi(sig) {
        return false;
    }
    // (4) resolves to a plain item body: a safe Rust-ABI `fn`, or a closure.
    let typing_env = mir_body.typing_env(tcx);
    if crate::tuple_layouts::resolution_may_reenter(tcx, called, args) {
        return false;
    }
    let Ok(Some(instance)) = ty::Instance::try_resolve(tcx, typing_env, called, args) else {
        return false;
    };
    let ty::InstanceKind::Item(resolved) = instance.def else { return false };
    if tcx.is_foreign_item(resolved) {
        return false;
    }
    match tcx.def_kind(resolved) {
        DefKind::Fn | DefKind::AssocFn => {
            let resolved_sig = tcx.fn_sig(resolved).skip_binder().skip_binder();
            if !sig_is_safe_rust_abi(resolved_sig) {
                return false;
            }
        }
        // A closure body is the only non-fn item a safe `Fn*::call*` resolves
        // to as `Item`. A coroutine shares `DefKind::Closure` and resolves as
        // `Item` from `Coroutine::resume`; it is outside what this root has
        // measured (and never returns a bare `Box`), so it is refused.
        DefKind::Closure if !tcx.is_coroutine(resolved) => {
            // A closure inherits its enclosing `fn`'s target features.
            if has_extern_indicator_or_target_feature(tcx, tcx.typeck_root_def_id(resolved)) {
                return false;
            }
        }
        _ => return false,
    }
    // (5) no user axiom, (6) no extern indicator / naked / target feature — on
    // BOTH the item the call names and the body that runs.
    if has_extern_indicator_or_target_feature(tcx, called)
        || carries_user_axiom(tcx, called)
        || (resolved != called
            && (has_extern_indicator_or_target_feature(tcx, resolved)
                || carries_user_axiom(tcx, resolved)))
    {
        return false;
    }
    true
}

/// `Safety::Safe` outright and a `Rust` / `rust-call` ABI.
fn sig_is_safe_rust_abi(sig: ty::FnSig<'_>) -> bool {
    matches!(sig.safety(), rustc_hir::Safety::Safe)
        && matches!(sig.abi(), rustc_abi::ExternAbi::Rust | rustc_abi::ExternAbi::RustCall)
}

/// The MIR blocks of `mir_body` whose `Call` terminator is a returned-`Box`
/// validity root, keyed exactly as `convert` numbers extracted blocks
/// (`BlockId(bb.as_usize())`). The compiler hands this to trust-vcgen; see the
/// module doc.
pub fn returned_box_root_call_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
) -> FxHashSet<trust_types::BlockId> {
    let mut out = FxHashSet::default();
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        if let mir::TerminatorKind::Call { func, destination, .. } = &bb_data.terminator().kind {
            if call_is_returned_box_validity_root(tcx, mir_body, func, *destination) {
                out.insert(trust_types::BlockId(bb.as_usize()));
            }
        }
    }
    out
}

/// `#[trust::assume_total]` / `#[trust::skip]` on `def_id`, on any ancestor
/// (impl block, module, enclosing fn of a closure), or on the self type of the
/// impl a method lives in — the reach of `trust_verify::item_has_trust_attr`,
/// plus ancestors of every kind. Over-refusing here only loses a root.
fn carries_user_axiom(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let is_axiom = |attr: &rustc_attr_ir::Attribute| {
        if matches!(attr, rustc_attr_ir::Attribute::Parsed(_)) {
            return false;
        }
        matches!(
            attr.path().as_slice(),
            [tool, name] if tool.as_str() == "trust"
                && USER_AXIOM_ATTRS.contains(&name.as_str())
        )
    };
    let has_axiom = |did: DefId| {
        #[allow(deprecated)]
        let attrs = tcx.get_all_attrs(did);
        attrs.iter().any(|attr| is_axiom(attr))
    };
    let mut current = Some(def_id);
    while let Some(did) = current {
        if attrs_queryable(tcx, did) {
            if has_axiom(did) {
                return true;
            }
            if matches!(tcx.def_kind(did), DefKind::Impl { .. }) {
                let self_adt =
                    tcx.type_of(did).instantiate_identity().skip_normalization().ty_adt_def();
                if let Some(adt) = self_adt {
                    if attrs_queryable(tcx, adt.did()) && has_axiom(adt.did()) {
                        return true;
                    }
                }
            }
        }
        current = tcx.opt_parent(did);
    }
    false
}

/// An extern indicator, `#[naked]`, or any target feature on `def_id`.
/// A def with no codegen attributes to read is treated as HAVING one (refused):
/// every def reaching here is a `fn`, associated `fn` or closure, so that arm is
/// unreachable today and exists only to round toward NO.
fn has_extern_indicator_or_target_feature(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.def_kind(def_id).has_codegen_attrs() {
        return true;
    }
    let attrs = tcx.codegen_fn_attrs(def_id);
    attrs.contains_extern_indicator()
        || attrs.flags.contains(CodegenFnAttrFlags::NAKED)
        || !attrs.target_features.is_empty()
}

/// Mirror of `trust_verify::attrs_queryable`: ancestors whose attributes rmeta
/// never encoded ICE when queried cross-crate. Skipping one only skips a place
/// an axiom could not be written anyway.
fn attrs_queryable(tcx: TyCtxt<'_>, did: DefId) -> bool {
    if did.is_local() {
        return true;
    }
    !matches!(
        tcx.def_kind(did),
        DefKind::ForeignMod
            | DefKind::ExternCrate
            | DefKind::Use
            | DefKind::AnonConst
            | DefKind::OpaqueTy
            | DefKind::GlobalAsm
            | DefKind::TyParam
            | DefKind::ConstParam
            | DefKind::LifetimeParam
            | DefKind::SyntheticCoroutineBody
            | DefKind::Static { nested: true, .. }
    )
}

/// The extractor twin's root test for `local`: the local's ONLY terminator
/// definition (a `Call` destination, a `Yield` resume place, an `InlineAsm`
/// output) is ONE whole-local `Call` that
/// [`call_is_returned_box_validity_root`] admits.
///
/// Only a ROOT test. The caller (`convert::origin_of_box_local`) must itself
/// have refused a local with a whole-local `Assign`, an escaped/borrowed slot or
/// a projected write, and a parameter — otherwise the call found here is not the
/// only thing that ever wrote the local.
pub(crate) fn sole_call_def_is_returned_box_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    local: mir::Local,
) -> bool {
    let whole = |p: &mir::Place<'_>| p.local == local && p.projection.is_empty();
    let mut root_call = None;
    let mut defs = 0usize;
    for bb_data in mir_body.basic_blocks.iter() {
        match &bb_data.terminator().kind {
            mir::TerminatorKind::Call { func, destination, .. } if whole(destination) => {
                defs += 1;
                root_call = Some((func, *destination));
            }
            mir::TerminatorKind::Yield { resume_arg, .. } if whole(resume_arg) => defs += 1,
            mir::TerminatorKind::InlineAsm { operands, .. } => {
                defs += operands
                    .iter()
                    .filter(|op| {
                        matches!(op,
                            mir::InlineAsmOperand::Out { place: Some(p), .. }
                            | mir::InlineAsmOperand::InOut { out_place: Some(p), .. }
                            if whole(p))
                    })
                    .count();
            }
            _ => {}
        }
        if defs > 1 {
            return false;
        }
    }
    defs == 1
        && root_call.is_some_and(|(func, destination)| {
            call_is_returned_box_validity_root(tcx, mir_body, func, destination)
        })
}

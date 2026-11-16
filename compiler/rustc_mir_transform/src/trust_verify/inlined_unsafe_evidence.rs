//! Trust (O2-inline, 2026-09-24): AN UNSAFE OPERATION'S ROW MUST SURVIVE THE
//! OPTIMIZER THAT DELETES THE OPERATION.
//!
//! `TrustVerify` reads the fully optimized MIR. At `-O` (MIR inlining and GVN
//! run at `mir-opt-level >= 2`) two things happen to an unsafe operation the
//! user wrote, and each deletes the only MIR construct its fail-closed row was
//! keyed on:
//!
//! * **An `unsafe fn` call is INLINED.** At `-O0` every call to a rustc-unsafe
//!   callee is a `Call` terminator and gets a row keyed on it: the compiler's
//!   `[unsafe:unmodeled-call]` (`synthetic_unmodeled_unsafe_call_vcs`) when
//!   `call_has_unsafe_model_keyed` says Trust has no model, and otherwise the
//!   model's own vcgen rows (`[unsafe:sep:call]`, `[unsafe:sep:from_u32_unchecked]`,
//!   the `[unsafe] missing SAFETY comment` stand-in, …), which are ALSO minted
//!   from that `Call` terminator and its operands. Inlining removes the
//!   terminator, so BOTH kinds of row vanish. What is left is the callee's
//!   body — whose own operations sit in a sysroot-inlined scope that every
//!   sysroot-inline exemption (the vcgen trusted-std spans, D8-P0's
//!   `scope_is_inlined_from_sysroot`) excuses as "std's obligation". That
//!   premise is true of std's SAFE API and false of an `unsafe fn`, whose
//!   precondition is precisely the CALLER's obligation.
//! * **GVN folds the evidence.** A user reborrow of a raw deref, `&*p`, with `p`
//!   a known constant pointer, is evaluated to a constant reference: the
//!   `Rvalue::Ref` of `*p` — the place the `[unsafe:sep:deref]` rows and the
//!   stand-in were minted from — is gone, and `_0 = const {0x4 as &u32}` is all
//!   that remains.
//!
//! Measured on stage-1 `a8c853de6f` (probes under the session scratchpad
//! `wave1/O2-inline/`), each of these built rc=0 at `-Copt-level=2` on the
//! verifying lane and is refused at `-O0`:
//!
//! | probe | shape | `-O2` binary |
//! |---|---|---|
//! | `n_neo` | `transmute_neo::<usize, Box<u32>>(4)` into `f(b: Box<u32>)` | SIGSEGV (139) |
//! | `n_slice` | `slice::from_raw_parts(NonNull::dangling().as_ptr(), 4)` into `f(&[u32])` | SIGSEGV (139) |
//! | `n_rawref` | `&*NonNull::dangling().as_ptr()` as `&'static u32`, then `*mk()` | SIGSEGV (139) |
//! | `n_asref` | `NonNull::dangling().as_ref()`, then `*mk()` | SIGSEGV (139) |
//! | `n_asrefp` | `p.as_ref()` of a `NonNull` PARAMETER, returned `&'static` | (lib) |
//! | `n_char` | `char::from_u32_unchecked(0xD800)` | invalid `char` |
//! | `n_utf8` | `str::from_utf8_unchecked(b)` of an arbitrary `&[u8]` | (lib) |
//! | `n_wop` | `&*ptr::without_provenance::<u32>(8)` | (lib) |
//!
//! Two rows close it, each keyed on what the optimizer CANNOT delete.
//!
//! # 1. `[unsafe:inlined-unsafe-call]`, keyed on the inlined SCOPE
//!
//! The inliner never deletes a scope: every inlined callee leaves a
//! `SourceScopeData { inlined: Some((instance, callsite_span)), .. }`, which
//! survives GVN, DCE and CFG simplification even when every statement in it was
//! folded away (`n_neo`'s `mk` is `scope 1 (inlined transmute_neo) {}` over one
//! `const Box(0x4)` statement). [`inlined_unsafe_call_sites`] charges each
//! inlined scope whose callee is a fn item that rustc deems unsafe TO CALL from
//! the code that called it (the same rule `synthetic_unmodeled_unsafe_call_vcs`
//! mirrors from `check_unsafety`: unsafe signature and not a safe
//! target-feature fn, or target features the caller lacks), when that caller is
//! NOT an authenticated sysroot def. A sysroot caller is std calling its own
//! unsafe API inside a SAFE std function that was itself inlined — std's
//! obligation under the same premise every other sysroot-inline discharge rests
//! on; the user's side of that edge is the safe call, which has no
//! precondition.
//!
//! The row is charged for EVERY such callee, modeled or not. The `-O0` set
//! "unsafe callees with no model" (`!call_has_unsafe_model_keyed`) is the wrong
//! set after inlining: a model is a row minted from the `Call` terminator and
//! its operands, and the terminator is exactly what inlining removed. Measured:
//! `transmute_neo`, `slice::from_raw_parts`, `char::from_u32_unchecked` and
//! `str::from_utf8_unchecked` are all `modeled=true` at `-O0` and all lost their
//! row at `-O2`. So after inlining NO unsafe callee is modeled, and the row is
//! the `-O0` unmodeled-call row applied to the whole set. It is always-SAT, so a
//! body that inlines an unsafe callee from its own code is refused at `-O`
//! exactly as an unmodeled call is refused at `-O0`.
//!
//! ONE exemption, keyed on the HIR, never on a name: a callsite whose span is
//! the call-expression span of a call the compiler generated INSIDE an
//! `UnsafeSource::CompilerGenerated` unsafe block (`format_args!`'s
//! `Arguments::new`, `.await`'s `Pin::new_unchecked`/`get_context`) is the
//! compiler's own desugaring, not user unsafe; see
//! [`compiler_generated_unsafe_call_spans`]. A user call can never carry such a
//! span (`format_args!` hoists every user argument into a `super let` OUTSIDE
//! the block, and an innermost `UserProvided` block always wins), and a span
//! mismatch of any kind fails CLOSED — the row stays.
//!
//! Shims are not charged: only `InstanceKind::Item` of a `Fn`/`AssocFn` is a
//! call the user wrote. Drop glue (`drop_in_place` is an `unsafe fn`, inlined
//! as `InstanceKind::DropGlue` at every `Drop` terminator) is the compiler's.
//!
//! # 2. `[unsafe:folded-invalid-constant]`, keyed on the FOLD RESULT
//!
//! GVN folds `&*p` (and a `transmute` of a constant) only when it can evaluate
//! it, and what it produces is a constant. A constant that is not a valid value
//! of its type — a dangling, null, unaligned or out-of-allocation reference or
//! `Box`, a `bool` that is not 0/1, a surrogate `char`, an enum with no variant
//! for its discriminant, a zero `NonZero` — is evidence that the program
//! manufactured it by an unsafe operation whose row the fold deleted, and it
//! cannot arise any other way: a `const` item or promoted with such a value is
//! rejected by const-eval's own validation, and a safe std function does not
//! return one. [`folded_invalid_constant_sites`] runs the interpreter's own
//! (non-recursive) validity check (`InterpCx::validate_operand`, the check Miri
//! runs on every typed copy) over every `mir::Const::Val` whose type has
//! RESTRICTED validity somewhere by value ([`type_has_restricted_validity`]), in
//! every statement and terminator of the body — every scope, because copy
//! propagation can move the folded constant into a statement of an inlined
//! callee's scope after the user's own statement dies.
//!
//! The interpreter is the CTFE machine with alignment ENFORCED
//! (`mk_eval_cx_for_trust_folded_const_validity`). GVN folds with `DummyMachine`,
//! which does not enforce alignment, and the validity check checks a
//! reference's alignment only when its machine does — so under `DummyMachine` a
//! misaligned but dereferenceable reference nested anywhere in a folded
//! aggregate would pass.
//!
//! # Cost, measured
//!
//! At `-O0` neither row can fire: the MIR inliner is off below
//! `mir-opt-level 2` (and no sysroot fn is `#[rustc_force_inline]`), and GVN is
//! off, so every constant is a const-eval-validated one. Trust (-O parity,
//! 2026-09-25): the same now holds at a plain `-O` in a verifying session, which
//! runs `mir-opt-level 1` at every `-Copt-level` unless `-Zmir-opt-level` is given
//! (`rustc_session::trust_default_mir_opt_level_by_flags`); what follows is the
//! cost under an EXPLICIT `-Zmir-opt-level >= 2` or `-Zinline-mir=yes`, the only
//! sessions these rows still cover. There the row
//! refuses an unsafe callee whose precondition the `-O0` lane PROVED through its
//! model (`get_unchecked` under a bound, `from_u32_unchecked` under a guard);
//! measured, the `get_unchecked` control is ALREADY refused at `-O2` (its
//! inlined raw deref carries unprovable `[unsafe:sep:deref]` rows), and the
//! guarded `from_u32_unchecked` compiled at `-O2` only because nothing charged
//! it at all. `u8::unchecked_add` under a proved precondition compiled at `-O2`
//! (its inlined `AddUnchecked` carries a provable overflow row) but is refused at
//! `-O0` as an unmodeled call; this row restores `-O0` parity for it. No passing
//! `tests/ui/trust` fixture compiled at `-O` makes a user-written call to an
//! unsafe fn.

use rustc_const_eval::const_eval::{
    CompileTimeInterpCx, mk_eval_cx_for_trust_folded_const_validity,
};
use rustc_const_eval::interpret::{InterpErrorKind, MemoryKind, PlaceTy};

use super::*;

/// Recursion bound for [`type_has_restricted_validity`]; hitting it answers
/// `true` (validate — the validator is the judge, not this filter).
const RESTRICTED_VALIDITY_DEPTH_LIMIT: u32 = 16;

/// Is a call to `callee` (instantiated by `args`) unsafe when made from code
/// owned by `caller`? The rule `synthetic_unmodeled_unsafe_call_vcs` mirrors
/// from rustc's `check_unsafety`: an unsafe signature that is not a safe
/// target-feature fn, or target features the caller does not enable.
fn call_is_unsafe<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    args: ty::GenericArgs<'tcx>,
    caller: DefId,
) -> bool {
    let cg = tcx.codegen_fn_attrs(callee);
    let unsafe_sig = matches!(
        tcx.fn_sig(callee).instantiate(tcx, args).skip_binder().safety(),
        rustc_hir::Safety::Unsafe
    );
    let target_feature_unsafe = !tcx.is_target_feature_call_safe(
        &cg.target_features,
        // `body_codegen_attrs`, as rustc's own `check_unsafety` reads it: the
        // caller may be a closure, a coroutine or a const-like body.
        &tcx.body_codegen_attrs(caller).target_features,
    );
    (unsafe_sig && !cg.safe_target_features) || target_feature_unsafe
}

/// The spans of every call expression in `local`'s own HIR body whose
/// innermost enclosing unsafe block is `UnsafeSource::CompilerGenerated` —
/// recorded as the span the MIR `Call` terminator's `fn_span` (and so an
/// inlined scope's callsite span) carries: `expr.span` for `ExprKind::Call`,
/// the `fn_span` field for `ExprKind::MethodCall` (THIR's `mirror_expr`).
///
/// Only a LOCAL fn/closure owner with a real HIR body answers; everything else
/// (a Clean-origin def, a by-move coroutine body, a const) answers the empty
/// set, so its inlined unsafe calls stay charged (fail-closed). Nested bodies
/// (closures, inline consts) are not descended into: each is its own owner.
pub(super) fn compiler_generated_unsafe_call_spans(
    tcx: TyCtxt<'_>,
    local: LocalDefId,
) -> FxHashSet<rustc_span::Span> {
    use rustc_hir::intravisit::{self, Visitor};
    if crate::clean_origin_mir::is_clean_origin(tcx, local)
        || !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
    {
        return FxHashSet::default();
    }
    let Some(hir_body) = tcx.hir_maybe_body_owned_by(local) else {
        return FxHashSet::default();
    };
    struct Finder {
        unsafe_blocks: Vec<rustc_hir::UnsafeSource>,
        spans: FxHashSet<rustc_span::Span>,
    }
    impl<'v> Visitor<'v> for Finder {
        fn visit_block(&mut self, block: &'v rustc_hir::Block<'v>) {
            let pushed = if let rustc_hir::BlockCheckMode::UnsafeBlock(source) = block.rules {
                self.unsafe_blocks.push(source);
                true
            } else {
                false
            };
            intravisit::walk_block(self, block);
            if pushed {
                self.unsafe_blocks.pop();
            }
        }
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            if matches!(self.unsafe_blocks.last(), Some(rustc_hir::UnsafeSource::CompilerGenerated))
            {
                match expr.kind {
                    rustc_hir::ExprKind::Call(..) => {
                        self.spans.insert(expr.span);
                    }
                    rustc_hir::ExprKind::MethodCall(_, _, _, fn_span) => {
                        self.spans.insert(fn_span);
                    }
                    _ => {}
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut finder = Finder { unsafe_blocks: Vec::new(), spans: FxHashSet::default() };
    finder.visit_body(hir_body);
    finder.spans
}

/// Every scope of `body` into which the MIR inliner copied an unsafe fn that
/// was called from non-sysroot code, as `(callsite span, callee)`. See the
/// module doc, section 1.
pub(super) fn inlined_unsafe_call_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(rustc_span::Span, DefId)> {
    let dbg = env_flag_enabled("TRUST_UNSAFE_CALL_DEBUG");
    let mut exempt_spans: FxHashMap<LocalDefId, FxHashSet<rustc_span::Span>> = FxHashMap::default();
    let mut sites = Vec::new();
    for scope_data in body.source_scopes.iter() {
        let Some((instance, callsite_span)) = scope_data.inlined else { continue };
        // Only an ordinary fn item is a call someone WROTE; shims (drop glue,
        // closure/fn-pointer adapters, …) are the compiler's.
        let ty::InstanceKind::Item(callee) = instance.def else { continue };
        if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn)
            || tcx.is_foreign_item(callee)
        {
            continue;
        }
        // The code that made the call: the nearest inlined instance of the
        // CALLSITE scope (the inliner attaches the callee's outermost scope as a
        // child of it), or this body itself when the call was in its own code.
        // An inlined scope always has a parent; were one ever missing, the body
        // itself is the conservative owner (its calls are charged).
        let owner =
            scope_data.parent_scope.and_then(|parent| parent.inlined_instance(&body.source_scopes));
        let caller = match owner {
            Some(owner) if trust_mir_extract::def_is_in_real_sysroot_crate(tcx, owner.def_id()) => {
                if dbg && call_is_unsafe(tcx, callee, instance.args, owner.def_id()) {
                    eprintln!(
                        "TRUST_UNSAFE_CALL_DEBUG: inlined-unsafe-call {:?} callee={} skipped: \
                         caller is sysroot {}",
                        body.source.def_id(),
                        tcx.def_path_debug_str(callee),
                        tcx.def_path_debug_str(owner.def_id()),
                    );
                }
                continue;
            }
            Some(owner) => owner.def_id(),
            None => body.source.def_id(),
        };
        if !call_is_unsafe(tcx, callee, instance.args, caller) {
            continue;
        }
        // The compiler's own desugaring (see `compiler_generated_unsafe_call_spans`).
        // Only this body's own ITEM code (not a promoted or shim body) or an
        // inlined local owner's HIR can answer.
        let hir_owner = match owner {
            None if body.source.promoted.is_none()
                && matches!(body.source.instance, ty::InstanceKind::Item(_)) =>
            {
                caller.as_local()
            }
            Some(owner) if matches!(owner.def, ty::InstanceKind::Item(_)) => caller.as_local(),
            _ => None,
        };
        if let Some(local) = hir_owner
            && exempt_spans
                .entry(local)
                .or_insert_with(|| compiler_generated_unsafe_call_spans(tcx, local))
                .contains(&callsite_span)
        {
            if dbg {
                eprintln!(
                    "TRUST_UNSAFE_CALL_DEBUG: inlined-unsafe-call {:?} callee={} skipped: \
                     compiler-generated unsafe block",
                    body.source.def_id(),
                    tcx.def_path_debug_str(callee),
                );
            }
            continue;
        }
        // PARITY with the `-O0` row's std-TCB discharge, under the SAME A/B gate
        // (`synthetic_unmodeled_unsafe_call_vcs`): a sysroot callee whose call
        // expression is std-authored source (a std macro's own tokens), decided
        // on the authenticated trusted-std table. Off unless the gate is set.
        if env_flag_enabled("TRUST_STD_UNSAFE_CALL_SKIP")
            && !callee.is_local()
            && trust_vcgen::span_is_trusted_std(
                &source_span_from_rustc_span(tcx, callsite_span),
                &trusted_std_source_files(tcx),
            )
        {
            continue;
        }
        if dbg {
            eprintln!(
                "TRUST_UNSAFE_CALL_DEBUG: inlined-unsafe-call {:?} callee={} CHARGED (caller {})",
                body.source.def_id(),
                tcx.def_path_debug_str(callee),
                tcx.def_path_debug_str(caller),
            );
        }
        sites.push((callsite_span, callee));
    }
    sites
}

/// Does `ty` have RESTRICTED validity somewhere by value — a leaf whose
/// invalid bit patterns a folded unsafe operation could produce: a reference,
/// `Box` or fn pointer (non-null, and for the first two aligned and
/// dereferenceable), `bool`, `char`, `!`, any enum (its discriminant), or a
/// pattern type (`NonZero`, `NonNull`)? A filter only —
/// the validator decides. Plain integers, floats and raw pointers accept every
/// initialized bit pattern, so a constant of them cannot be invalid. Unions
/// answer `false` (a union's validity does not constrain its fields); a field
/// the walk cannot normalize answers `true` (let the validator judge).
fn type_has_restricted_validity<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    depth: u32,
) -> bool {
    if depth > RESTRICTED_VALIDITY_DEPTH_LIMIT {
        return true;
    }
    if ty.is_box() {
        return true;
    }
    let recurse = |t: Ty<'tcx>| type_has_restricted_validity(tcx, typing_env, t, depth + 1);
    match *ty.kind() {
        // `ty::Pat` is a pattern type (`pattern_type!(u32 is 1..)`), which is
        // how `NonZero` and `NonNull` carry their niche.
        ty::Ref(..) | ty::FnPtr(..) | ty::Bool | ty::Char | ty::Never | ty::Pat(..) => true,
        ty::Array(elem, _) => recurse(elem),
        ty::Tuple(fields) => fields.iter().any(recurse),
        ty::Adt(def, _) if def.is_enum() => true,
        ty::Adt(def, args) if def.is_struct() => def.all_fields().any(|field| {
            match tcx.try_normalize_erasing_regions(typing_env, field.ty(tcx, args)) {
                Ok(field_ty) => recurse(field_ty),
                // Not seen through: let the validator judge.
                Err(_) => true,
            }
        }),
        _ => false,
    }
}

/// Is `constant` a value the interpreter's validity check rejects? `false` when
/// the check cannot be run at all for a reason that means "not a GVN fold"
/// (an `InvalidProgram` error: too generic, a layout error, an error already
/// reported); every other failure — a validation error, an unsupported
/// operation, a machine stop — answers `true` (fail-closed).
fn constant_is_invalid<'tcx>(
    ecx: &mut CompileTimeInterpCx<'tcx>,
    constant: &rustc_middle::mir::ConstOperand<'tcx>,
) -> bool {
    let decide = |err: rustc_const_eval::interpret::InterpErrorInfo<'tcx>| {
        !matches!(err.kind(), InterpErrorKind::InvalidProgram(_))
    };
    let op = match ecx.eval_mir_constant(&constant.const_, DUMMY_SP, None).report_err() {
        Ok(op) => op,
        Err(err) => return decide(err),
    };
    // An immediate constant has no address for the validator to walk: give it
    // one (the value is the constant's own bytes, copied without validation —
    // the CTFE machine's `enforce_validity` is `false` for an inhabited layout
    // unless `-Zextra-const-ub-checks`).
    let place = match ecx.allocate(op.layout, MemoryKind::Stack).report_err() {
        Ok(place) => place,
        Err(err) => return decide(err),
    };
    if let Err(err) = ecx.copy_op(&op, &place).report_err() {
        return decide(err);
    }
    match ecx
        .validate_place(
            &PlaceTy::from(place),
            /* recursive */ false,
            /* reset_provenance_and_padding */ false,
        )
        .report_err()
    {
        Ok(()) => false,
        Err(err) => decide(err),
    }
}

/// Every constant operand of `body`'s statements and terminators whose type
/// has restricted validity by value and whose value is not valid, as
/// `(span of the statement/terminator using it, type)`. See the module doc,
/// section 2. Debug-info constants and `required_consts` are not scanned: the
/// first has no runtime effect and the second is never a folded value.
pub(super) fn folded_invalid_constant_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(rustc_span::Span, Ty<'tcx>)> {
    use rustc_middle::mir::visit::Visitor;
    struct Scan<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        ecx: CompileTimeInterpCx<'tcx>,
        hits: Vec<(rustc_span::Span, Ty<'tcx>)>,
    }
    impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
        fn visit_const_operand(
            &mut self,
            constant: &rustc_middle::mir::ConstOperand<'tcx>,
            location: rustc_middle::mir::Location,
        ) {
            let rustc_middle::mir::Const::Val(_, ty) = constant.const_ else { return };
            if !type_has_restricted_validity(self.tcx, self.typing_env, ty, 0) {
                return;
            }
            if constant_is_invalid(&mut self.ecx, constant) {
                if env_flag_enabled("TRUST_UNSAFE_CALL_DEBUG") {
                    // No trimmed paths (the X2 ICE shape).
                    let rendered = rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                        "{:?}: {ty}",
                        constant.const_
                    ));
                    eprintln!(
                        "TRUST_UNSAFE_CALL_DEBUG: folded-invalid-constant {:?} CHARGED {rendered}",
                        self.body.source.def_id(),
                    );
                }
                self.hits.push((self.body.source_info(location).span, ty));
            }
        }
    }
    let typing_env = body.typing_env(tcx);
    let mut scan = Scan {
        tcx,
        body,
        typing_env,
        ecx: mk_eval_cx_for_trust_folded_const_validity(tcx, typing_env),
        hits: Vec::new(),
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        scan.visit_basic_block_data(bb, data);
    }
    scan.hits
}

/// The `[unsafe:inlined-unsafe-call]` and `[unsafe:folded-invalid-constant]`
/// rows for `body`: always-SAT, forced `Failed` by
/// `refute_unsafe_demand_findings` (the `[unsafe` marker).
/// Trust (2026-10-02, KNOWN_HAZARDS "under an explicit `-Zinline-mir=yes` (or
/// `-Zmir-opt-level=2`), an inlined std panic is a tolerated runtime-checked row"):
/// every call the USER's body made to a NON-LOCAL callee (std, or a dependency)
/// whose inlined copy carries a PANIC PATH, as `(callsite span, callee)`, once per
/// callsite. A panic path is an `Assert` terminator or a diverging `Call` (no return
/// target), anywhere in that callee's inlined scope tree.
///
/// At `-O0` such a call keeps its `Call` terminator and its own call-site row
/// (`o.unwrap()`, `s.split_at(k)` are refused there). Inlining removes the call and
/// leaves the callee's panic in the caller, where a retained `Assert` reads as "the
/// compiler retained the existing assertion" and the default policy tolerates it:
/// rc 0 and the program panics. The row restores the `-O0` refusal, keyed on the
/// inlined scope, which the optimizer never deletes. A LOCAL callee is not charged:
/// inlining it moves its own asserts, which its own verification already reads the
/// same way. At `-O0` (and at a plain `-O` in a verifying session) the MIR inliner is
/// off, so this can fire only under an explicit `-Zinline-mir=yes` or
/// `-Zmir-opt-level >= 2`.
pub(super) fn inlined_panic_path_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(rustc_span::Span, DefId)> {
    let mut seen: FxHashSet<rustc_span::Span> = FxHashSet::default();
    let mut sites = Vec::new();
    for block in body.basic_blocks.iter() {
        let terminator = block.terminator();
        let panics = match &terminator.kind {
            TerminatorKind::Assert { .. } => true,
            TerminatorKind::Call { target, .. } => target.is_none(),
            _ => false,
        };
        if !panics {
            continue;
        }
        // The OUTERMOST inlined scope above this terminator: the call the body's
        // own code made (deeper inlined scopes are that callee's own calls).
        let mut scope = Some(terminator.source_info.scope);
        let mut outermost = None;
        while let Some(current) = scope {
            let data = &body.source_scopes[current];
            if let Some(inlined) = data.inlined {
                outermost = Some(inlined);
            }
            scope = data.parent_scope;
        }
        let Some((instance, callsite_span)) = outermost else { continue };
        let callee = instance.def_id();
        if callee.is_local() || !seen.insert(callsite_span) {
            continue;
        }
        sites.push((callsite_span, callee));
    }
    sites
}

pub(super) fn inlined_unsafe_evidence_vcs<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_path: &str,
) -> Vec<VerificationCondition> {
    let row = |span: rustc_span::Span, message: String| VerificationCondition {
        kind: VcKind::Assertion { message },
        function: trust_types::Symbol::intern(def_path),
        location: source_span_from_rustc_span(tcx, span),
        // Always SAT = always a finding: the operation's own row was deleted
        // by the optimizer and nothing re-derives it.
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
        // Not a contract-derived VC: no obligation to back-reference.
        obligation: None,
    };
    let mut vcs = Vec::new();
    for (span, callee) in inlined_unsafe_call_sites(tcx, body) {
        // No trimmed paths: rendering with them installs rustc's "a diagnostic
        // must be emitted" expectation (the X2 ICE shape).
        let name = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(callee));
        vcs.push(row(
            span,
            format!(
                "[unsafe:inlined-unsafe-call] call to `{name}` (unsafe fn) was inlined by the \
                 optimizer, which deletes the call-site row its precondition is charged on; the \
                 precondition is not proved (fail-closed — the same obligation an unmodeled \
                 unsafe call carries unoptimized)"
            ),
        ));
    }
    for (span, callee) in inlined_panic_path_sites(tcx, body) {
        let name = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(callee));
        vcs.push(row(
            span,
            format!(
                "[inlined-panic-path] call to `{name}` was inlined by the optimizer with a \
                 panic path; unoptimized, the call keeps its own call-site row, here the \
                 panic would read as a retained runtime check (fail-closed)"
            ),
        ));
    }
    for (span, ty) in folded_invalid_constant_sites(tcx, body) {
        let ty = rustc_middle::ty::print::with_no_trimmed_paths!(ty.to_string());
        vcs.push(row(
            span,
            format!(
                "[unsafe:folded-invalid-constant] the optimizer folded an operation into a \
                 constant of type `{ty}` that is not a valid value (a reference/Box must be \
                 non-null, aligned and dereferenceable); the unsafe operation that made it has \
                 no surviving row (fail-closed)"
            ),
        ));
    }
    vcs
}

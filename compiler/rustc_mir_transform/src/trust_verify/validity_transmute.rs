//! Trust (D8-P0, 2026-09-23): VALIDITY IS CHARGED WHERE IT IS MANUFACTURED.
//!
//! Two holes, one principle: a value whose type carries a *validity* invariant
//! that Trust's roots rely on (a `Box<T>`, a `&T`, a `&mut T`) must either come
//! from a channel that establishes the invariant, or carry a fail-closed row at
//! the place it was made.
//!
//! # 1. `transmute` into a `Box`/reference carried no obligation
//!
//! The extractor models `Rvalue::Cast(CastKind::Transmute, ..)` into a `Box` as a
//! plain `Cast` (`trust-mir-extract` `convert.rs`, the `ty.is_box()` arm) on the
//! stated assumption that "the deref's own validity obligation handles pointee
//! validity SEPARATELY". Commit `047d35ba90`'s Box-PARAMETER validity root made
//! that assumption false: `fn f(b: Box<u32>) -> u32 { *b }` mints no deref rows,
//! because every caller is verified — and nothing in the caller charged the
//! transmute. Measured on stage-1 `7766459729` (`decide/critic/o_tmute.rs`,
//! `decide/D8/ch/h1_*`): `f(mk())` with `mk() = transmute::<usize, Box<u32>>(4)`
//! built rc=0 and SIGSEGV'd (exit 139). The `&T` twin (`h3`: a transmuted null
//! `&'static u32`, then `*mk()`) did the same, and `h6` (a local's address
//! lifetime-extended to `&'static` by an identity-modulo-regions transmute)
//! verified rc=0. The other channels into a `Box` (`mem::zeroed`,
//! `MaybeUninit::assume_init`, `transmute_copy`, `ptr::read`, `Box::from_raw`,
//! union reads) carry a refusing row at O0; at `-O` an INLINED sysroot `unsafe
//! fn` loses its call-site row (measured by the review: `transmute_neo` into a
//! `Box`, `slice::from_raw_parts` of a dangling pointer, `NonNull::as_ref` all
//! build rc=0 at `-O2` and exit 139) — a separate, recorded gap this module does
//! not close.
//!
//! [`validity_transmute_vcs`] closes that one channel: every transmute whose
//! TARGET type is not inert (see [`transmute_target_carries_invariant`] — a
//! `Box`/`&`/`&mut` first of all, and fail-closed on everything that is not
//! plain bits) mints an always-SAT `[unsafe:validity-transmute]` row, which
//! `refute_unsafe_demand_findings` forces `Failed` like every other `[unsafe`
//! finding. Sites come from TWO places:
//!
//! * the body's own HIR `transmute` calls, typed by `typeck`
//!   ([`hir_transmute_call_sites`]). This half is REQUIRED, not belt-and-braces:
//!   `InstSimplify` (every opt-level) rewrites a transmute that is identity
//!   after region erasure into a plain copy, so `h6`'s
//!   `transmute::<&'a u32, &'static u32>` is simply absent from the MIR
//!   `TrustVerify` reads (measured: `mk`'s `-O0` MIR is `_0 = &_1; return`);
//! * every `Transmute` cast of the optimized MIR — which is what sees a
//!   transmute INLINED at `-O` from a callee whose HIR is not this body's —
//!   minus two exemptions, each keyed on an identity the user cannot forge,
//!   never on a name or a rendered path:
//!   - the statement's NEAREST inlined instance is a def of the compiler's own,
//!     artifact-authenticated sysroot (`def_is_in_real_sysroot_crate`). At `-O`
//!     the inliner copies std's own transmutes (`from_utf8_unchecked`'s
//!     `&[u8] -> &str`, `fmt::rt::Argument`'s `NonNull` packing) into user
//!     bodies; their validity is std's obligation under the same std premise
//!     every other sysroot-inlined discharge already rests on. A user closure
//!     inlined INTO a sysroot body has its own (local) nearest inlined
//!     instance, so it is not exempt;
//!   - rustc's own coroutine lowering between `&mut Context<'_>` and
//!     `ResumeTy`'s private `NonNull<Context>` field
//!     ([`is_compiler_coroutine_context_transmute`]).
//!
//!   Neither MIR exemption can hide a transmute the user wrote in THIS body: the
//!   HIR half charges it regardless.
//!
//! Measured on 2026-09-23 (stage-1 `--emit=mir -Zmir-include-spans`, O0 and O2):
//! across the ~400 passing `tests/ui/trust` fixtures, the only user-scope
//! transmutes into a non-inert type are the 76 coroutine-context casts of the
//! async fixtures, and the 40 `tests/ordinary-rust-sweep` programs have no
//! user-scope transmute into a non-inert type at all; no passing verify-on
//! fixture calls `transmute` in its source.
//!
//! There is deliberately NO identity exemption (`&'a T -> &'static T` is
//! region-erased identity and is exactly `h6`'s attack).
//!
//! # 2. `#[trust::assume_total]` swallowed unsafe operations
//!
//! `verification_decision` skipped an `assume_total` body wholesale, so every
//! validity row inside it vanished with its panic rows (critic `k3`: a raw deref
//! of address 4 became one caller-side runtime-checked row, rc=0; `k4`: a
//! transmute into `Box` left only an `ASSUMPTION [assumed-total]` line; `k5_bin`:
//! that `Box` fed the Box-parameter root, rc=0, exit 139). Totality is not
//! validity. [`assume_total_cannot_cover_body`] names the bodies the attribute
//! may NOT skip: any that can perform an unsafe operation. Such a body is
//! verified in full, exactly as if the attribute were absent — the ONLY split
//! that is sound without classifying each row as "totality" or "validity"
//! (a misclassified validity row would be a false proof; e.g. the alignment
//! checks rustc inserts are MIR `Assert`s, i.e. look like panics).
//!
//! Trust (2026-09-30): the same rule for a callee's `requires`, which a skipped
//! body charges at no call, is `uncharged_callable::assume_total_cannot_cover_calls`,
//! asked when this module's predicate answers `false`.

use super::*;

/// Recursion bound for [`transmute_target_carries_invariant`]. Hitting it
/// answers `true` (fail closed).
const VALIDITY_TYPE_DEPTH_LIMIT: u32 = 16;

/// May a value of `ty` MANUFACTURED BY TRANSMUTE violate an invariant that some
/// consumer relies on? The question is asked the fail-closed way round: only a
/// type every bit pattern of which is a valid, safe value is INERT, and every
/// other type — the `Box`/`&T`/`&mut T` the validity roots trust first of all —
/// carries an invariant.
///
/// Inert (answers `false`):
/// * integers and floats (every initialized bit pattern is a value);
/// * raw pointers to a sized pointee, a slice or `str` (no validity beyond
///   initialization; any deref keeps its own `[unsafe:sep:*]` row). A raw
///   pointer to any OTHER unsized pointee (`*const dyn Trait` needs a valid
///   vtable) is not inert;
/// * arrays, tuples, and non-`Box` STRUCTS and UNIONS whose every (normalized)
///   field is inert. A union is NOT inert by itself: `MaybeUninit<Box<T>>`
///   promises nothing, but its later `assume_init()` is a sysroot read whose
///   call row `-O` inlining deletes (see the union arm), so the transmute INTO
///   it is where the charge must sit.
///
/// Carries an invariant (answers `true`): `&T`, `&mut T`, `Box` (checked FIRST —
/// `Box` is a struct); `bool`, `char`, every `enum` (discriminant validity), `!`,
/// fn pointers and fn items' neighbours (`FnPtr` is non-null), pattern types
/// (`NonNull`/`NonZero`/`Vec`'s capacity niche — so `Vec`, `String`, `Rc`, … are
/// charged too: their safety invariants are what std's safe API relies on), and
/// everything the walk cannot see through (`Param`, an alias that does not
/// normalize, `Dynamic`, `Foreign`, closures, coroutines, …) or deeper than
/// [`VALIDITY_TYPE_DEPTH_LIMIT`].
///
/// The memo (`dq_D8-returned-box.md` step 1) asked only for "contains a
/// `Box`/`&`/`&mut` by value". This is a superset in the REFUSING direction:
/// measured on 2026-09-23, no passing `tests/ui/trust` fixture and none of the
/// 40 `tests/ordinary-rust-sweep` programs transmutes into ANY type in user
/// scope (beyond rustc's own `.await` lowering, exempted structurally below), so
/// the widening costs nothing measured, and it closes the `bool`/`char`/`enum`/
/// `fn`-pointer/`Vec` creation channels in the same stroke.
pub(super) fn transmute_target_carries_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    carries_at_depth(tcx, typing_env, ty, 0)
}

fn carries_at_depth<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    depth: u32,
) -> bool {
    if depth > VALIDITY_TYPE_DEPTH_LIMIT {
        return true;
    }
    // `Box` is a struct: it must be decided before the struct arm.
    if ty.is_box() {
        return true;
    }
    let recurse = |t: Ty<'tcx>| carries_at_depth(tcx, typing_env, t, depth + 1);
    match *ty.kind() {
        ty::Int(_) | ty::Uint(_) | ty::Float(_) => false,
        ty::RawPtr(pointee, _) => {
            !(matches!(pointee.kind(), ty::Slice(_) | ty::Str) || pointee.is_sized(tcx, typing_env))
        }
        ty::Array(elem, _) => recurse(elem),
        ty::Tuple(fields) => fields.iter().any(recurse),
        // Trust (D8-P0 review, 2026-09-23): a UNION is walked like a struct, NOT
        // treated as inert. "Reading the field later is charged by
        // `[unsafe:union-field]`" is false at `-O`: `transmute::<usize,
        // MaybeUninit<Box<u32>>>(4).assume_init()` reads the field inside
        // core's inlined `assume_init`, the unsafe call's row is lost to
        // inlining, and GVN folds the whole body to `const Box(0x4)` — measured
        // on stage-1 `-O2`: rc=0 on the verifying lane, then SIGSEGV (exit 139)
        // through the Box-parameter root. `MaybeUninit<u32>` stays inert.
        ty::Adt(def, args) if def.is_struct() || def.is_union() => def.all_fields().any(|field| {
            match tcx.try_normalize_erasing_regions(typing_env, field.ty(tcx, args)) {
                Ok(field_ty) => recurse(field_ty),
                // A field type that does not normalize is a type the walk
                // cannot see through: fail closed.
                Err(_) => true,
            }
        }),
        // Ref, Bool, Char, Never, FnPtr, FnDef, Pat, Str, Slice (unsized — not a
        // transmute target), enums, Param, Alias, Dynamic, Foreign, Closure,
        // Coroutine*, UnsafeBinder, Error, and the inference/placeholder kinds.
        _ => true,
    }
}

/// The nearest inlined instance of `scope` is a def of the compiler's own,
/// artifact-authenticated sysroot.
pub(super) fn scope_is_inlined_from_sysroot<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    scope: rustc_middle::mir::SourceScope,
) -> bool {
    scope.inlined_instance(&body.source_scopes).is_some_and(|instance| {
        trust_mir_extract::def_is_in_real_sysroot_crate(tcx, instance.def_id())
    })
}

/// Is `pointee` the `core::task::Context` lang item?
fn is_task_context<'tcx>(tcx: TyCtxt<'tcx>, pointee: Ty<'tcx>) -> bool {
    matches!(
        *pointee.kind(),
        ty::Adt(def, _) if tcx.is_lang_item(def.did(), rustc_attr_ir::lang_items::LangItem::Context)
    )
}

/// rustc's own coroutine lowering (`coroutine/mod.rs`), recognized
/// STRUCTURALLY, in a coroutine body only. Two shapes, both between the task
/// context reference and `core::future::ResumeTy`'s private
/// `NonNull<Context<'static>>` field:
///
/// * `transform_async_context`, at entry: `move _2 as NonNull<Context<'_>>
///   (Transmute)` where `_2` is `CTX_ARG` (after the swap, the `&mut Context<'_>`
///   resume argument — every user-visible use of it was renamed away, so user
///   code cannot reach this local);
/// * `eliminate_get_context_calls`, at each `.await`: `copy (resume.0:
///   NonNull<Context<'_>>) as &mut Context<'_> (Transmute)` where `resume:
///   ResumeTy` (field 0 is private to `core`, so user code cannot spell it).
///
/// Neither exemption can hide a transmute the USER wrote in this body: those
/// are charged from the HIR ([`hir_transmute_call_sites`]) whatever the MIR
/// looks like. Measured: these two shapes are the only user-scope transmutes
/// into a non-inert type in the passing `tests/ui/trust` fixtures (76 sites, all
/// in the async fixtures), at O0 and O2.
fn is_compiler_coroutine_context_transmute<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &rustc_middle::mir::Operand<'tcx>,
    target: Ty<'tcx>,
) -> bool {
    use rustc_middle::mir::ProjectionElem;
    if body.coroutine.is_none() {
        return false;
    }
    let Some(place) = operand.place() else {
        return false;
    };
    // Entry shape: `CTX_ARG as NonNull<Context<'_>>`.
    if place.as_local() == Some(crate::coroutine::CTX_ARG) {
        let operand_ty = place.ty(&body.local_decls, tcx).ty;
        let operand_is_context_ref = matches!(
            *operand_ty.kind(),
            ty::Ref(_, pointee, rustc_hir::Mutability::Mut) if is_task_context(tcx, pointee)
        );
        let Some(resume_ty) = tcx.lang_items().resume_ty() else { return false };
        let resume_def = tcx.adt_def(resume_ty);
        let Some(resume_field) = resume_def.non_enum_variant().fields.iter().next() else {
            return false;
        };
        let field_adt = tcx
            .type_of(resume_field.did)
            .instantiate_identity()
            .skip_normalization()
            .ty_adt_def()
            .map(|def| def.did());
        let target_is_resume_field = match *target.kind() {
            ty::Adt(def, args) => {
                Some(def.did()) == field_adt
                    && args.types().next().is_some_and(|pointee| is_task_context(tcx, pointee))
            }
            _ => false,
        };
        return operand_is_context_ref && target_is_resume_field;
    }
    // `.await` shape: `ResumeTy.0 as &mut Context<'_>`.
    let ty::Ref(_, pointee, rustc_hir::Mutability::Mut) = *target.kind() else {
        return false;
    };
    if !is_task_context(tcx, pointee) {
        return false;
    }
    let Some((base, ProjectionElem::Field(field, _))) = place.as_ref().last_projection() else {
        return false;
    };
    if field.as_usize() != 0 {
        return false;
    }
    let base_ty = base.ty(&body.local_decls, tcx).ty;
    matches!(
        *base_ty.kind(),
        ty::Adt(resume_def, _) if tcx.is_lang_item(resume_def.did(), rustc_attr_ir::lang_items::LangItem::ResumeTy)
    )
}

/// Every `transmute`/`transmute_unchecked` CALL written in this body's own HIR
/// whose (typeck) output type holds a Box/reference by value.
///
/// # Why the optimized MIR alone is not enough (measured 2026-09-23)
///
/// `TrustVerify` reads the fully optimized MIR, and `InstSimplify` runs at every
/// opt-level (`mir-opt-level >= 1`, i.e. `-O0` too). Its `simplify_cast` turns a
/// transmute whose operand and target types are EQUAL AFTER REGION ERASURE into
/// a plain `Use`. `transmute::<&'a u32, &'static u32>(&x)` — the lifetime-
/// extension attack `h6` — is exactly such a cast: the `-O0` MIR of `h6`'s `mk`
/// is `_0 = &_1; return` with no transmute left to see. The HIR call, and its
/// type in `typeck`, survive every MIR pass.
///
/// Only an ordinary item body (`InstanceKind::Item`, not promoted) of a LOCAL
/// fn/closure is scanned: a shim's `def_id` names a DIFFERENT body's HIR. A
/// closure's HIR is its own body (the visitor does not descend into nested
/// bodies), and it is verified — and scanned — separately.
fn hir_transmute_call_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(rustc_span::Span, Ty<'tcx>)> {
    use rustc_hir::intravisit::{self, Visitor};
    if body.source.promoted.is_some() || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return Vec::new();
    }
    let Some(local) = body.source.def_id().as_local() else { return Vec::new() };
    // A Clean-origin def has no HIR (see `def_uses_unsafe_source_impl`).
    if crate::clean_origin_mir::is_clean_origin(tcx, local) {
        return Vec::new();
    }
    // Only a fn/closure owner has a walkable HIR body of its own (a tuple
    // constructor, say, has MIR and no HIR body; `SyntheticCoroutineBody` is a
    // by-move COPY whose parent coroutine is scanned when it is verified).
    if !matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
        return Vec::new();
    }
    let Some(hir_body) = tcx.hir_maybe_body_owned_by(local) else { return Vec::new() };
    let typeck = tcx.typeck(local);
    let typing_env = body.typing_env(tcx);

    struct Finder<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'a ty::TypeckResults<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        hits: Vec<(rustc_span::Span, Ty<'tcx>)>,
    }
    impl<'a, 'tcx> Visitor<'tcx> for Finder<'a, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Call(callee, _) = expr.kind
                && let Some(callee_ty) = self.typeck.expr_ty_opt(callee)
                && let ty::FnDef(did, _) = *callee_ty.kind()
                && self.tcx.intrinsic(did).is_some_and(|intrinsic| {
                    intrinsic.name == sym::transmute || intrinsic.name == sym::transmute_unchecked
                })
            {
                // A transmute call with no recorded output type is not seen
                // through: charge it (the `Never` stand-in is only a label).
                let holds_and_ty = match self.typeck.expr_ty_opt(expr) {
                    Some(out) => {
                        let holds = match self.tcx.try_normalize_erasing_regions(
                            self.typing_env,
                            ty::Unnormalized::new_wip(out),
                        ) {
                            Ok(out) => {
                                transmute_target_carries_invariant(self.tcx, self.typing_env, out)
                            }
                            // A type that does not normalize is not seen through.
                            Err(_) => true,
                        };
                        (holds, out)
                    }
                    None => (true, self.tcx.types.never),
                };
                if holds_and_ty.0 {
                    self.hits.push((expr.span, holds_and_ty.1));
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut finder = Finder { tcx, typeck, typing_env, hits: Vec::new() };
    finder.visit_body(hir_body);
    finder.hits
}

/// Every site in `body` that manufactures a Box/reference-holding value by
/// transmute, as `(span, target type)`: the HIR `transmute` calls of the body's
/// own source ([`hir_transmute_call_sites`]), plus every `Transmute` cast of the
/// optimized MIR outside the two exempt shapes (the MIR half is what sees a
/// transmute INLINED from a non-sysroot callee at `-O`). A MIR cast whose span is
/// already a HIR site is not charged twice.
pub(super) fn validity_transmute_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(rustc_span::Span, Ty<'tcx>)> {
    use rustc_middle::mir::{CastKind, Rvalue, StatementKind};
    let typing_env = body.typing_env(tcx);
    let mut sites = hir_transmute_call_sites(tcx, body);
    let hir_spans: FxHashSet<rustc_span::Span> = sites.iter().map(|(span, _)| *span).collect();
    for bb in body.basic_blocks.iter() {
        for statement in &bb.statements {
            let StatementKind::Assign(assign) = &statement.kind else { continue };
            let Rvalue::Cast(CastKind::Transmute, operand, target) = &assign.1 else {
                continue;
            };
            let target = *target;
            if !transmute_target_carries_invariant(tcx, typing_env, target) {
                continue;
            }
            if scope_is_inlined_from_sysroot(tcx, body, statement.source_info.scope) {
                continue;
            }
            if is_compiler_coroutine_context_transmute(tcx, body, operand, target) {
                continue;
            }
            if hir_spans.contains(&statement.source_info.span) {
                continue;
            }
            sites.push((statement.source_info.span, target));
        }
    }
    sites
}

/// The `[unsafe:validity-transmute]` rows for `body`: always-SAT, forced
/// `Failed` by `refute_unsafe_demand_findings` (the `[unsafe` marker).
pub(super) fn validity_transmute_vcs<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_path: &str,
) -> Vec<VerificationCondition> {
    validity_transmute_sites(tcx, body)
        .into_iter()
        .map(|(span, target)| VerificationCondition {
            kind: VcKind::Assertion {
                // No trimmed paths: rendering a `Ty` with them installs rustc's
                // "a diagnostic must be emitted" expectation (the X2 ICE shape).
                message: rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "[unsafe:validity-transmute] transmute produces `{target}`, a type with a \
                     validity or safety invariant (a Box/reference must be non-null, aligned, \
                     dereferenceable and live) that transmuted bits are not proved to satisfy \
                     (fail-closed — a Box or reference parameter is trusted valid because its \
                     creation is charged here)"
                )),
            },
            function: trust_types::Symbol::intern(def_path),
            location: source_span_from_rustc_span(tcx, span),
            // Always SAT = always a finding: nothing models the transmuted bits.
            formula: trust_types::Formula::Bool(true),
            contract_metadata: None,
            // Not a contract-derived VC: no obligation to back-reference.
            obligation: None,
        })
        .collect()
}

/// May `#[trust::assume_total]` skip this body? `true` means it may NOT: the body
/// can perform an unsafe operation, whose validity obligation totality does not
/// cover, so it is verified in full.
///
/// A body qualifies when (any of):
/// * its own source is an unsafe context or holds a user-written `unsafe` block
///   (`def_uses_user_unsafe_source`: `unsafe fn`, or a `UserProvided` unsafe
///   block anywhere in its HIR, macro-expanded ones included; a
///   compiler-generated desugaring block such as `format_args!`'s is not user
///   unsafe);
/// * it has an edge into code this compilation does not verify, as the ONE
///   enumeration (`unverified_edges`, rule `AssumedTotal`) names it: a call that
///   does not resolve to a local body held to this rule or to the sysroot at an
///   instantiation that reaches no foreign user code (a local foreign item, a
///   verify-off dependency fn, a virtual or unresolvable callee), an indirect
///   call, a foreign static read, a function pointer or vtable minted for such
///   code, open drop glue, or inline assembly;
/// * it contains a validity transmute (redundant with the first arm today; kept
///   so the two halves of this module cannot drift apart).
///
/// Only LOCAL bodies are re-classified: a foreign body in a declared bundling
/// scope has no HIR here, and its assume_total skip already refuses at the reuse
/// gate (`None` from the query) — returning `Verify` for it would be a widening.
pub(super) fn assume_total_cannot_cover_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    let def_id = body.source.def_id();
    if !def_id.is_local() {
        return false;
    }
    if matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
        && def_uses_user_unsafe_source(tcx, def_id)
    {
        return true;
    }
    // Trust (r15, 2026-10-01): every other edge into code this compilation does
    // not verify — a call (a local foreign item, a verify-off dependency fn, a
    // sysroot callee instantiated at foreign user code, a virtual or unresolvable
    // callee), an indirect call, a foreign static read, a function pointer or
    // vtable created for such code, open drop glue — comes from the ONE
    // enumeration (`unverified_edges`). The foreign-call and foreign-static arms
    // this replaces are two of its kinds. MEASURED before on stage-1 `ae0494648a`:
    // `#[trust::assume_total] fn t(x: u32) -> u32 { dep::null_fn(); x }` (a
    // verify-off dependency whose safe `null_fn` writes through a null pointer)
    // was skipped in default, strict and memory-safe, built rc=0, and every
    // binary died with SIGSEGV (139).
    !assume_total_unverified_edges(tcx, body).is_empty()
        || !validity_transmute_sites(tcx, body).is_empty()
}

/// The edges of `body` into code this compilation does not verify, under the
/// `#[trust::assume_total]` rule (the sysroot is held at an instantiation that
/// reaches no foreign user code). Rendered for the revocation warning.
pub(super) fn assume_total_unverified_edges<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<String> {
    super::unverified_edges::unverified_edges(
        tcx,
        body,
        super::unverified_edges::EdgeRule::AssumedTotal,
    )
    .into_iter()
    .map(|edge| edge.what)
    .collect()
}

/// Tell the user why an `#[trust::assume_total]` body is being verified anyway.
/// Emitted from `verification_decision`, which can run more than once per body;
/// the diagnostic context deduplicates identical diagnostics.
pub(super) fn warn_assume_total_does_not_cover_unsafe<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) {
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id));
    let mut diag = tcx.dcx().struct_span_warn(
        tcx.def_span(def_id),
        format!(
            "Trust: `#[trust::assume_total]` on `{path}` does not cover its unsafe operations \
             or its edges into code this compilation does not verify; the body is verified in \
             full"
        ),
    );
    diag.note(
        "`assume_total` assumes TOTALITY (no panic, termination), never VALIDITY: an unsafe \
         operation (raw deref, transmute, union read, unsafe or foreign call) can manufacture a \
         value that a verified caller trusts, so its obligation must survive the attribute",
    );
    let edges = assume_total_unverified_edges(tcx, body);
    if !edges.is_empty() {
        diag.note(format!(
            "the body also reaches code this compilation does not verify, whose validity \
             totality does not cover either: {}",
            edges.join("; ")
        ));
    }
    diag.help(
        "move the unsafe operation into a separate function without `#[trust::assume_total]` \
         so it is verified on its own, and keep the attribute on the safe remainder",
    );
    diag.emit();
}

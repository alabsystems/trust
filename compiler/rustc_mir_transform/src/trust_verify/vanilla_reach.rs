//! Trust (VANILLA-REACH-1, 2026-10-27): the vanilla class decided by REACH as
//! well as by type.
//!
//! [`super::callee_is_vanilla_sysroot`] admits a sysroot callee to the policy-B
//! vanilla class ("its unproved panic is std's own defined behaviour, reported as
//! a runtime-checked row") only when every type argument and every parameter type
//! of the instance is FOUNDATIONAL: built from std/core/alloc types alone. That
//! refuses every std routine instantiated at a LOCAL data type, whatever the
//! routine does with it. Measured on the two harness repos (2026-10-27,
//! `docs/DECISION_QUEUE.md` VANILLA-REACH-1): `Option::<&V>::is_some`,
//! `BTreeMap::<String, V>::get::<str>` and `Vec::<(&str, Option<Fate>, &[String])>::push`
//! for local `V`/`Fate` were each a fatal "generic absent callee" row, while the
//! same calls at `String` were tolerated.
//!
//! THE EXTENSION. A call the type rule refuses is admitted when ALL of:
//!
//!  1. every exclusion of the type rule still passes — no user global allocator,
//!     not the deliberately-unbundled division family, not a known caller-value
//!     panic, not an inexact float intrinsic, not a hash-table caller-value panic —
//!     and the callee is in the REAL sysroot (`core`/`alloc`/`std`; the hash-table
//!     crate's StdSite credit is not extended);
//!  2. the callee is in NO panic family vcgen charges at the call site
//!     (`trust_vcgen::callee_has_call_site_panic_family`: `unwrap`/`expect`, the
//!     allocation sinks, the division and overflow families, the slice-method
//!     panics, the index mutators, ...) and is not an `Index`/`IndexMut` method.
//!     Those recognizers were measured at foundational types; this extension does
//!     not rely on them firing at a local type, so a call in any such family keeps
//!     the type rule's answer;
//!  3. the SPELLED instantiation (the callee's type arguments and its instantiated
//!     parameter types) is PLAIN DATA (see [`ty_is_plain_data`]): scalars, `str`,
//!     references, raw pointers, arrays, slices and tuples of plain data, real
//!     sysroot ADTs at plain arguments, and LOCAL ADTs whose instantiated fields are
//!     plain data and which have no hand-written impl of a sysroot trait outside a
//!     short LAW-FREE allow-list (`Drop`, `Clone`, `Copy`, `Default`, `From`,
//!     `TryFrom`, `AsRef`, `AsMut`, the markers): a builtin `#[derive]` expansion
//!     of any trait is admitted, a hand-written or
//!     `#[automatically_derived]`-claimed `Ord`, `Eq`, `Hash`, `Borrow`,
//!     `Iterator`, `Display`, `Debug`, `io::Read`, `Deref`, `Error`, operator, ...
//!     impl is not, and a union is not plain. No type
//!     parameter, inference variable, trait object, function pointer, function
//!     item, closure, coroutine, foreign type or unnormalized alias appears, and no
//!     ADT of a dependency (an allowlisted TCB crate included);
//!  3b. the masking walk (`ty_reaches_foreign_user_code`, which reads a sysroot
//!     ADT's declared fields where (3) stops at its arguments) finds no type in
//!     the instantiation through which code outside this compilation can run — a
//!     `dyn` or a `fn` pointer in a std field (`io::Error`'s custom payload unless
//!     IOERROR-PAYLOAD-1 closes it, a `Waker`'s vtable) keeps the call out. Without
//!     it the admission would rest on (4) alone, whose walk takes a virtual call or
//!     a `dyn` drop on a HANDED value as a leaf (CALL-REACH-1 D2: judged where the
//!     value was made) — a premise built for withdrawing credits, not granting them;
//!  4. CALL-REACH-1 closes the call (`sysroot_drop_reach::call_site_reach` answers
//!     `ClosedByPrefilter` or `ClosedByWalk`): every body the instance can execute is
//!     a sysroot body or a local body held by induction
//!     (`local_item_is_held_to_this_rule`: local, not `#[trust::skip]`, with MIR),
//!     and the walk found no edge into code this compilation does not verify.
//!
//! WHY IT IS SOUND (the argument VANILLA-REACH-1 records row by row). The class
//! says one thing: an unproved panic of the call is a RUNTIME CHECK of defined
//! behaviour, disclosed as a runtime-checked row, and the call runs no code nothing
//! verified. (4) is exactly CALL-REACH-1's closure: the only non-sysroot code the
//! instance can run is this crate's own bodies, each verified as its own root (a
//! failing one fails the build; a trait impl method's `requires` is refused on
//! every fail-closed lane by `trait_impl_requires`). (2) keeps every caller-value
//! panic the type rule's argument already excludes or vcgen charges, so admitting
//! the call grants no caller-value panic a pass. (3)'s lawful-trait conjunct keeps
//! out the one channel through which a VERIFIED, panic-free local body can still
//! make std panic: a broken LAW of a sysroot trait std relies on — a non-total
//! `Ord`, an inconsistent `Eq`/`Hash`/`Borrow`, an iterator's lying length, a
//! formatting impl that returns `Err` on its own, an `io::Read` that over-reports —
//! which std answers with a panic, an abort or non-termination. It is an
//! allow-list: only traits std relies on for nothing but the body's own panics may
//! be hand-written. A builtin derive is structurally lawful over lawful fields, and
//! the fields are walked.
//!
//! WHAT IT DOES NOT CHANGE. The certify lane refuses every runtime-checked row as
//! before. The non-reentrant callee set vcgen's inferred recursion-termination lane
//! reads (`VcgenContext::nonreentrant_callees`) keeps the TYPE rule only: a call
//! admitted here may run a local body, which may re-enter the caller.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::{Body, Operand};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use rustc_span::{ExpnKind, MacroKind, Spanned, sym};

use super::sysroot_drop_reach::{CallReach, call_site_reach};

/// How deep [`ty_is_plain_data`] follows nested local ADT fields before it
/// answers `false` (fail-closed).
const PLAIN_DATA_MAX_DEPTH: u32 = 32;

/// The admission described in the module doc. `vanilla_exclusions_pass` is the
/// type rule's own exclusion verdict for this callee (conjunct 1 above, computed by
/// the caller with the inputs it already holds).
pub(super) fn callee_is_vanilla_sysroot_by_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    vanilla_exclusions_pass: bool,
    name: &str,
) -> bool {
    // Every refusal before the walk names its conjunct in the debug trace, so a
    // fixture can show WHICH conjunct keeps a call out.
    let refuse = |why: &str| {
        if super::env_flag_enabled("TRUST_VANILLA_DEBUG") {
            eprintln!("[VANILLA_REACH] admitted=false refused={why} callee=`{name}`");
        }
        false
    };
    if !vanilla_exclusions_pass {
        return refuse("type-rule-exclusion");
    }
    let Some((def_id, generic_args)) = func.const_fn_def() else {
        return refuse("not-a-fn-item");
    };
    // A synthetic spelling (`__trust_total_clone`, `__trust_try_total`, ...) keys
    // many callees under one ledger name; the extension never speaks for one.
    if name.starts_with("__trust_") || name.contains("::<__trust_") {
        return refuse("synthetic-name");
    }
    if !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id) {
        return refuse("not-core-alloc-std");
    }
    if trust_vcgen::callee_has_call_site_panic_family(name)
        || trust_vcgen::callee_is_root_call_caller_value_panic(name)
    {
        return refuse("panic-family");
    }
    if def_is_index_method(tcx, def_id) {
        return refuse("index-method");
    }
    if generic_args.has_non_region_param()
        || generic_args.has_non_region_infer()
        || generic_args.has_non_region_placeholders()
    {
        return refuse("not-monomorphic");
    }
    let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    let sig = tcx.instantiate_bound_regions_with_erased(
        tcx.fn_sig(def_id).instantiate(tcx, generic_args).skip_normalization(),
    );
    for t in generic_args.types().chain(sig.inputs().iter().copied()) {
        if let Err(why) = plain_data_verdict(tcx, t, &mut memo, PLAIN_DATA_MAX_DEPTH) {
            return refuse(&format!("not-plain-data({why})"));
        }
    }
    // Conjunct 3b: the masking walk, which reads a sysroot ADT's DECLARED fields
    // (`ty_is_plain_data` stops at a sysroot ADT's arguments), finds no type
    // through which code outside this compilation can run: a `dyn` or a `fn`
    // pointer in a std field (`io::Error`'s custom payload, a `Waker`'s vtable)
    // keeps the call out, unless IOERROR-PAYLOAD-1 closes that `dyn`.
    let mut foreign_memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    if generic_args
        .types()
        .chain(sig.inputs().iter().copied())
        .any(|t| super::ty_reaches_foreign_user_code(tcx, t, &mut foreign_memo))
    {
        return refuse("reaches-foreign-user-code");
    }
    let verdict = rustc_middle::ty::print::with_no_trimmed_paths!(call_site_reach(
        tcx, body, typing_env, func, args
    ));
    let admitted = matches!(verdict, CallReach::ClosedByPrefilter | CallReach::ClosedByWalk);
    if super::env_flag_enabled("TRUST_VANILLA_DEBUG") {
        let label = match &verdict {
            CallReach::NotJudged => "not-judged".to_string(),
            CallReach::ClosedByPrefilter => "closed(prefilter)".to_string(),
            CallReach::ClosedByWalk => "closed(walk)".to_string(),
            CallReach::CoveredByCaller => "covered-by-caller".to_string(),
            CallReach::Open(why) | CallReach::OpenWithdrawingBundled(why) => format!("open: {why}"),
        };
        eprintln!("[VANILLA_REACH] admitted={admitted} reach={label} callee=`{name}`");
    }
    admitted
}

/// Is `def_id` the method of an `Index`/`IndexMut` impl or the trait items
/// themselves? `v[i]`, `map[&k]` and `s[a..b]` panic on the caller's value; the
/// type rule admits them only at foundational types, where the call-site index
/// lanes were measured. This extension does not take them.
fn def_is_index_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let trait_did = tcx
        .trait_of_assoc(def_id)
        .or_else(|| tcx.trait_impl_of_assoc(def_id).map(|impl_did| tcx.impl_trait_id(impl_did)));
    trait_did.is_some_and(|t| {
        tcx.is_lang_item(t, LangItem::Index)
            || tcx.is_lang_item(t, LangItem::IndexMut)
            || tcx.is_diagnostic_item(sym::SliceIndex, t)
    })
}

/// [`ty_is_plain_data`] with a reason for the debug trace: the first local ADT
/// that has a hand-written impl outside the allow-list, or the kind of the first
/// type that is not plain. Decides exactly what [`ty_is_plain_data`] decides.
fn plain_data_verdict<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    memo: &mut FxHashMap<Ty<'tcx>, bool>,
    depth: u32,
) -> Result<(), String> {
    if ty_is_plain_data(tcx, ty, memo, depth) {
        return Ok(());
    }
    if !super::env_flag_enabled("TRUST_VANILLA_DEBUG") {
        return Err(String::new());
    }
    // Name the culprit (debug only): a local ADT with an unlawful impl, else the
    // first non-plain leaf kind the type walk meets.
    for inner in ty.walk() {
        let Some(t) = inner.as_type() else { continue };
        match t.kind() {
            ty::Adt(def, _) if def.is_union() => return Err(format!("union {t:?}")),
            ty::Adt(def, _)
                if def.did().is_local() && local_adt_has_unlawful_trait_impl(tcx, def.did()) =>
            {
                return Err(format!("hand-written impl on {t:?}"));
            }
            ty::Adt(def, _)
                if !def.did().is_local()
                    && !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def.did()) =>
            {
                return Err(format!("dependency ADT {t:?}"));
            }
            ty::Adt(def, args) if def.did().is_local() => {
                for field in def.all_fields() {
                    let field_ty =
                        tcx.type_of(field.did).instantiate(tcx, args).skip_normalization();
                    if field_ty.walk().any(|g| {
                        g.as_type().is_some_and(|f| {
                            matches!(
                                f.kind(),
                                ty::FnPtr(..) | ty::Dynamic(..) | ty::Closure(..) | ty::Param(_)
                            )
                        })
                    }) {
                        return Err(format!("field of {t:?} holds {field_ty:?}"));
                    }
                }
            }
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Ref(..)
            | ty::RawPtr(..)
            | ty::Array(..)
            | ty::Slice(_)
            | ty::Pat(..)
            | ty::Tuple(_)
            | ty::Adt(..) => {}
            ty::Closure(did, _) if trust_mir_extract::def_is_in_real_sysroot_crate(tcx, *did) => {}
            _ => return Err(format!("{t:?}")),
        }
    }
    Err(format!("{ty:?}"))
}

/// Conjunct 3 of the module doc: is `ty` plain data? Coinductive over recursive
/// local types (a cycle is plain unless something on it is not); bounded by
/// `depth` over nested local ADTs, answering `false` past it.
fn ty_is_plain_data<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    memo: &mut FxHashMap<Ty<'tcx>, bool>,
    depth: u32,
) -> bool {
    if let Some(&known) = memo.get(&ty) {
        return known;
    }
    memo.insert(ty, true);
    let verdict = match ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => true,
        ty::Ref(_, inner, _)
        | ty::RawPtr(inner, _)
        | ty::Array(inner, _)
        | ty::Slice(inner)
        | ty::Pat(inner, _) => ty_is_plain_data(tcx, *inner, memo, depth),
        ty::Tuple(elems) => elems.iter().all(|t| ty_is_plain_data(tcx, t, memo, depth)),
        ty::Adt(def, args) => {
            if !args.types().all(|t| ty_is_plain_data(tcx, t, memo, depth)) {
                false
            } else if def.is_union() {
                // A union's bytes are read as any of its fields; not plain
                // (fail-closed).
                false
            } else if def.did().is_local() {
                match depth.checked_sub(1) {
                    None => false,
                    Some(depth) => {
                        !local_adt_has_unlawful_trait_impl(tcx, def.did())
                            && def.all_fields().all(|field| {
                                let field_ty = tcx.type_of(field.did).instantiate(tcx, args);
                                match tcx.try_normalize_erasing_regions(
                                    ty::TypingEnv::fully_monomorphized(),
                                    field_ty,
                                ) {
                                    Ok(field_ty) => ty_is_plain_data(tcx, field_ty, memo, depth),
                                    Err(_) => false,
                                }
                            })
                    }
                }
            } else {
                // A real sysroot ADT: its own fields are std's; what a type
                // parameter carries in was asked above. A dependency ADT (an
                // allowlisted TCB crate included) and std's hash-table crate's
                // ADT at top level are not plain.
                trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def.did())
            }
        }
        // A closure DEFINED in core/alloc/std (`decode_repr`'s, `map_err`'s inside
        // an `io::Error` method): its body is the sysroot's, and what it holds and
        // takes are asked here like any other type.
        ty::Closure(did, args) if trust_mir_extract::def_is_in_real_sysroot_crate(tcx, *did) => {
            let closure = args.as_closure();
            let sig = tcx.instantiate_bound_regions_with_erased(closure.sig());
            closure
                .parent_args()
                .iter()
                .filter_map(|arg| arg.as_type())
                .chain(closure.upvar_tys().iter())
                .chain(sig.inputs_and_output.iter())
                .all(|t| ty_is_plain_data(tcx, t, memo, depth))
        }
        // Everything else — a type parameter, an inference variable, `dyn Trait`, a
        // function pointer or item, a local or dependency closure, a coroutine, a
        // foreign type, an unnormalized alias — is not plain data (fail-closed).
        _ => false,
    };
    memo.insert(ty, verdict);
    verdict
}

/// Does the local ADT `adt` have a LOCAL hand-written impl of a SYSROOT trait that
/// std may rely on beyond panic-freedom? A sysroot generic routine instantiated at
/// `adt` can run `adt`'s impls of sysroot traits (it names no other trait). Each
/// such body is verified as its own root, so a PANIC in it is charged there; what
/// verification does not hold it to is the trait's LOGIC, and for several sysroot
/// traits std documents a panic, an abort or non-termination when that logic is
/// broken: a non-total `Ord` (`sort`), an inconsistent `Eq`/`Hash`/`Borrow` or a
/// non-deterministic `Hasher` (the hash tables, "unspecified behaviour of the map"),
/// an iterator's lying `size_hint` (`ExactSizeIterator::len`'s assertion, a
/// `with_capacity(lower)` capacity overflow), a formatting impl that returns `Err`
/// on its own (`ToString::to_string` and `format` panic), an `io::Read` that
/// reports more bytes than it was given. So this is an ALLOW-LIST: every local impl
/// of a sysroot trait whose trait reference names `adt` anywhere (its `Self` type
/// or a trait argument: `impl PartialEq<Adt> for u32` counts) answers `true`
/// unless it is a builtin `#[derive]` expansion or its trait is one std relies on
/// for nothing but the body's own panics ([`law_free_trait_ids`]). A trait outside
/// the sysroot is not asked: a sysroot body is compiled without it and never calls
/// it.
fn local_adt_has_unlawful_trait_impl(tcx: TyCtxt<'_>, adt: DefId) -> bool {
    let law_free = law_free_trait_ids(tcx);
    for (trait_did, impls) in tcx.all_local_trait_impls(()) {
        if trait_did.is_local()
            || !trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, *trait_did)
            || law_free.contains(trait_did)
        {
            continue;
        }
        for impl_did in impls.iter().map(|local| local.to_def_id()) {
            let trait_ref =
                tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization();
            let names_adt = trait_ref.args.iter().any(|arg| {
                arg.walk().any(|inner| {
                    inner
                        .as_type()
                        .is_some_and(|t| matches!(t.kind(), ty::Adt(d, _) if d.did() == adt))
                })
            });
            if names_adt && !impl_is_builtin_derive(tcx, impl_did) {
                return true;
            }
        }
    }
    false
}

/// The sysroot traits a hand-written local impl of may stand in a plain-data type
/// ([`local_adt_has_unlawful_trait_impl`]): std calls their methods without
/// relying on any law of the result, so the only way the impl changes what a std
/// routine does is by panicking, which its own verification charges. `Drop` (its
/// body is verified as its own root; a `#[trust::skip]` one is not held,
/// CALL-REACH-1), `Clone`, `Copy`, `Default`, `From`, `TryFrom`, `AsRef`, `AsMut`.
/// A trait rustc does not name here (no lang or diagnostic item) is absent from the
/// list, which only makes the rule refuse more.
///
/// The auto-trait markers `Send`, `Sync` and `Unpin` are NOT on the list
/// (G2-STD-CALLEE-1 review, Finding 1). A hand-written `unsafe impl Send`/`Sync`
/// is an unsafe promise std's synchronization code relies on for data-race
/// freedom, and an `impl Unpin` one `Pin`'s guarantee rests on: breaking either is
/// undefined behaviour, not a panic the impl's own verification would charge, and
/// no body exists to verify. An auto-derived marker is no impl in
/// `all_local_trait_impls`, so only a type with an explicit marker impl is
/// refused here, and the policy-B fixture `vanilla_reach_local_plain_data.rs`
/// pins all three (`hand_send`, `hand_sync`, `hand_unpin`).
fn law_free_trait_ids(tcx: TyCtxt<'_>) -> Vec<DefId> {
    let lang = [LangItem::Drop, LangItem::Clone, LangItem::Copy];
    let diag = [sym::Default, sym::From, sym::TryFrom, sym::AsRef, sym::AsMut];
    lang.iter()
        .filter_map(|item| tcx.lang_items().get(*item))
        .chain(diag.iter().filter_map(|item| tcx.get_diagnostic_item(*item)))
        .collect()
}

/// Is `impl_did` the expansion of a BUILTIN `#[derive]` — a derive macro defined in
/// an authentic foundational crate? The `#[automatically_derived]` attribute alone
/// is user-writable and is not enough: rustc's `is_builtin_derived` also asks that
/// the impl came from a `Derive` expansion of a `#[rustc_builtin_macro]`, and this
/// asks that the macro be core's.
fn impl_is_builtin_derive(tcx: TyCtxt<'_>, impl_did: DefId) -> bool {
    let expn = tcx.def_span(impl_did).ctxt().outer_expn_data();
    tcx.is_builtin_derived(impl_did)
        && matches!(expn.kind, ExpnKind::Macro(MacroKind::Derive, _))
        && expn
            .macro_def_id
            .is_some_and(|m| !m.is_local() && super::crate_is_authentic_foundational(tcx, m.krate))
}

// trust-mir-extract/convert.rs: Convert MIR structures to trust-types
//
// Handles: BasicBlock, Statement, Terminator, Rvalue, Operand, Place, BinOp
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_middle::mir;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use trust_types::*;

use crate::ty_convert;

/// Trust: M6 rung-7 sweep — convert a rustc `Ty` through `convert_ty_in_env`
/// whenever a body `TypingEnv` is available, falling back to the plain
/// (env-less, alias/opaque-normalization-disabled) `convert_ty` only when it
/// is not (the handful of synthetic/in-process-compiler-test call sites that
/// never had a body in scope, matching the existing `local_decls:
/// Option<&LocalDecls>` fallback convention used throughout this module).
///
/// This is the SAME pattern the rung-7 closure-capture fix landed for
/// `AggregateKind::Closure`'s upvar conversion (see its call site below): a
/// type lowered independently of the enclosing body's other locals must go
/// through the identical entry point with the identical `typing_env` as
/// every other local, or it can silently diverge from an env-aware
/// conversion of the SAME nominal rustc `Ty` the instant the type recurses
/// through an alias/opaque position deep enough to need normalization
/// (`Ty::Unsupported` under `convert_ty` vs a resolved `Ty::Datatype`/`Ty::Adt`
/// under `convert_ty_in_env`). Routing every remaining env-less call site
/// through this one helper closes that class of divergence "by construction"
/// for the whole crate, not just for closures.
fn convert_ty_with_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
    ty: ty::Ty<'tcx>,
) -> Ty {
    match typing_env {
        Some(env) => ty_convert::convert_ty_in_env(tcx, env, ty),
        None => ty_convert::convert_ty(tcx, ty),
    }
}

/// Convert a rustc BasicBlock to our BasicBlock.
pub(crate) fn convert_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    bb: mir::BasicBlock,
    bb_data: &mir::BasicBlockData<'tcx>,
    local_decls: Option<&mir::LocalDecls<'tcx>>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> BasicBlock {
    let stmts: Vec<Statement> = bb_data
        .statements
        .iter()
        .map(|stmt| convert_statement(tcx, stmt, local_decls, typing_env))
        .collect();

    let terminator = convert_terminator(tcx, bb_data.terminator(), typing_env);

    BasicBlock { id: BlockId(bb.as_usize()), stmts, terminator }
}

/// Convert a rustc Statement.
fn convert_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    stmt: &mir::Statement<'tcx>,
    local_decls: Option<&mir::LocalDecls<'tcx>>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Statement {
    let span = convert_span(tcx, stmt.source_info.span);
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => Statement::Assign {
            place: convert_place(tcx, place, typing_env),
            rvalue: convert_rvalue(tcx, rvalue, local_decls, typing_env),
            span, // Trust: per-statement source span
        },
        mir::StatementKind::FakeRead(box (_, _)) => Statement::Nop,
        mir::StatementKind::SetDiscriminant { place, variant_index } => {
            Statement::SetDiscriminant {
                place: convert_place(tcx, place, typing_env),
                variant_index: variant_index.as_usize(),
            }
        }
        mir::StatementKind::StorageLive(local) => Statement::StorageLive(local.as_usize()),
        mir::StatementKind::StorageDead(local) => Statement::StorageDead(local.as_usize()),
        // Trust: rust 1.99 removed the standalone `StatementKind::Retag`; a retag is now
        // an operand-level annotation carried by `Rvalue::Use(_, WithRetag)`. A retag is
        // value-identity, so it contributes no functional statement to the extracted IR.
        mir::StatementKind::PlaceMention(place) => {
            Statement::PlaceMention(convert_place(tcx, place, typing_env))
        }
        mir::StatementKind::AscribeUserType(box (_, _), _) => Statement::Nop,
        mir::StatementKind::Coverage(_) => Statement::Coverage,
        mir::StatementKind::Intrinsic(box intrinsic) => {
            convert_nondiverging_intrinsic(tcx, intrinsic, span, typing_env)
        }
        mir::StatementKind::ConstEvalCounter => Statement::ConstEvalCounter,
        mir::StatementKind::Nop => Statement::Nop,
        mir::StatementKind::BackwardIncompatibleDropHint { .. } => Statement::Nop,
    }
}

fn convert_nondiverging_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    intrinsic: &mir::NonDivergingIntrinsic<'tcx>,
    span: SourceSpan,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Statement {
    match intrinsic {
        mir::NonDivergingIntrinsic::Assume(operand) => Statement::Intrinsic {
            name: "assume".to_string(),
            args: vec![convert_operand(tcx, operand, typing_env)],
        },
        mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
            let operands = vec![
                convert_operand(tcx, &copy.src, typing_env),
                convert_operand(tcx, &copy.dst, typing_env),
                convert_operand(tcx, &copy.count, typing_env),
            ];
            Statement::Unsupported {
                kind: "NonDivergingIntrinsic::CopyNonOverlapping".to_string(),
                detail: "memory copy side effects require explicit memory-model lowering"
                    .to_string(),
                operands,
                span,
            }
        }
    }
}

/// Fuel for the structural clone-totality recursion (bounds recursive types).
const CLONE_TOTALITY_FUEL: u32 = 32;

/// Sentinel callee name for a `Clone::clone` call PROVED panic-free by
/// `tcx_clone_is_total`. The bridge models a call to it as a total (havoc) call.
/// Canonical definition (single source of truth across producer/consumer) lives in
/// `trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL`.
pub(crate) use trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL;

/// Leaf-name set of std/alloc/core wrappers whose `Clone` DEEP-clones its contents
/// (dispatches Clone into its type-arg element(s)) and runs no user code at the
/// wrapper level — so the wrapper's clone is total IFF every element's clone is
/// total. Conservative (omissions only lose precision → fail-closed).
fn is_std_deep_clone_container(tcx: TyCtxt<'_>, did: rustc_span::def_id::DefId) -> bool {
    let path = crate::safe_def_path_str(tcx, did);
    let leaf = path.rsplit("::").next().unwrap_or(&path);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    matches!(
        leaf,
        "Box"
            | "Vec"
            | "VecDeque"
            | "Rc"
            | "Arc"
            | "Option"
            | "Result"
            | "BTreeMap"
            | "BTreeSet"
            | "BinaryHeap"
            | "LinkedList"
            | "Cow"
            | "Wrapping"
            | "Reverse"
    ) && (path.starts_with("std::") || path.starts_with("alloc::") || path.starts_with("core::"))
}

/// Std leaf types whose `Clone` is total irrespective of any type parameter.
fn is_element_free_total_std_adt(tcx: TyCtxt<'_>, did: rustc_span::def_id::DefId) -> bool {
    let path = crate::safe_def_path_str(tcx, did);
    matches!(
        path.as_str(),
        "alloc::string::String"
            | "std::string::String"
            | "core::cmp::Ordering"
            | "std::cmp::Ordering"
            | "core::time::Duration"
            | "std::time::Duration"
    ) || path.starts_with("core::num::NonZero")
        || path.starts_with("std::num::NonZero")
        // num-bigint arbitrary-precision integers are NON-generic (limbs are fixed
        // primitive `u32`/`u64`), so their hand-written `Clone` bottoms out in
        // primitives and runs NO user code (alloc-abort excluded, as everywhere in
        // this TCB). Mirrors the bridge's already-trusted `is_element_free_total_std_type`
        // (trust-ir-bridge/src/lower.rs:14708). DELIBERATELY excludes `num_rational::Ratio`
        // / `BigRational`: it IS generic, so `Ratio<UserType>` must stay field-aware
        // (`tcx_clone_is_total`'s derived arm recurses into `numer`/`denom`, which now
        // bottom out here at `BigInt` — total — while a user element still fails closed).
        || (path.starts_with("num_bigint")
            && (path.ends_with("::BigInt") || path.ends_with("::BigUint")))
}

/// True iff `<ty as Clone>::clone` is PROVABLY panic-free (total), WITHOUT an axiom.
/// This runs at the tcx level (it sees CONCRETE generic args), so unlike the
/// bridge's `clone_is_total` it works for TYPE-ERASED containers (`Vec<K>`, whose
/// `RawVec` erases `K`): a primitive/`str`/`!`; a pointer / `FnDef`/`FnPtr` (cloning
/// COPIES the pointer, no pointee clone); a tuple/array/slice of totals; an ADT whose
/// `Clone` impl is `#[automatically_derived]` (a `#[derive(Clone)]`) with all field
/// types total; a known std deep-clone container all of whose type-arg elements are
/// total; or an element-free std leaf. Everything else — a hand-written/foreign
/// non-container `Clone` — is fail-closed `false`, so e.g. `Vec<PanickingK>::clone`
/// (whose `K` has a hand-written `Clone`) stays UNKNOWN (no false-PROVE). Fuel-bounded;
/// a recursive type short-circuits to `true` on cycle (sound: cycles arise only inside
/// derived/container chains, which are panic-free by construction).
fn tcx_clone_is_total<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    clone_method: rustc_span::def_id::DefId,
    fuel: u32,
    seen: &mut std::collections::HashSet<ty::Ty<'tcx>>,
) -> bool {
    use rustc_middle::ty::TyKind;
    if fuel == 0 {
        return false;
    }
    if !seen.insert(ty) {
        return true; // cycle inside a derived/container chain → panic-free by construction
    }
    // A non-monomorphic type (a type/const param, e.g. `ArrayVec<T, const N>`) must NOT reach the
    // `fully_monomorphized` `Instance::try_resolve` below: it ICEs ("cannot find N in param-env").
    // Fail closed — a generic impl is not a concrete provably-total method (it is verified per
    // monomorphization / compositionally instead).
    if ty.has_non_region_param() {
        return false;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never => true,
        TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::FnPtr(..) | TyKind::FnDef(..) => true,
        TyKind::Tuple(elems) => {
            elems.iter().all(|e| tcx_clone_is_total(tcx, e, clone_method, fuel - 1, seen))
        }
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            tcx_clone_is_total(tcx, *elem, clone_method, fuel - 1, seen)
        }
        // A pattern type (`pattern_type!(u32 is 0..=N)`) is a range-constrained primitive --
        // e.g. the inner field of the `Nanoseconds` niche type. Its clone is the base int's
        // clone: total iff the base is. (Reached via a derived niche wrapper's field recursion.)
        TyKind::Pat(base, _) => tcx_clone_is_total(tcx, *base, clone_method, fuel - 1, seen),
        TyKind::Adt(def, args) => {
            let did = def.did();
            // (a) a `#[derive(Clone)]` (`#[automatically_derived]`) impl dispatches Clone
            //     into the fields — total iff every field type is total. Resolve the
            //     concrete `<ty as Clone>::clone` to find and classify the impl.
            let derived = ty::Instance::try_resolve(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                clone_method,
                tcx.mk_args(&[ty.into()]),
            )
            .ok()
            .flatten()
            .is_some_and(|inst| {
                let impl_did = tcx.parent(inst.def_id());
                matches!(tcx.def_kind(impl_did), rustc_hir::def::DefKind::Impl { .. })
                    && tcx.is_automatically_derived(impl_did)
            });
            if derived {
                return def.all_fields().all(|f| {
                    tcx_clone_is_total(
                        tcx,
                        f.ty(tcx, args).skip_normalization(),
                        clone_method,
                        fuel - 1,
                        seen,
                    )
                });
            }
            // (b) a known std deep-clone container: total iff all type-arg elements are
            //     total (the wrapper runs no user code; the `Global` allocator is total).
            if is_std_deep_clone_container(tcx, did) {
                return args
                    .types()
                    .all(|t| tcx_clone_is_total(tcx, t, clone_method, fuel - 1, seen));
            }
            let path = crate::safe_def_path_str(tcx, did);
            // (b') HashMap/HashSet: `Clone` deep-clones the entries (K::clone + V::clone) and
            //      copies the table structure WITHOUT re-hashing (no user `Hash` call), so it is
            //      total iff every type arg's clone is total -- incl. the `RandomState` hasher /
            //      `Global` allocator, whose clones are themselves total. (NOT added to the
            //      shared `is_std_deep_clone_container`, which `tcx_derived_trait_is_total` also
            //      uses: `eq` HASHES keys, so HashMap needs its key-Hash check there, not this.)
            let leaf = path.rsplit("::").next().unwrap_or(&path);
            let leaf = leaf.split('<').next().unwrap_or(leaf);
            if matches!(leaf, "HashMap" | "HashSet")
                && (path.starts_with("std::") || path.starts_with("hashbrown::"))
            {
                return args
                    .types()
                    .all(|t| tcx_clone_is_total(tcx, t, clone_method, fuel - 1, seen));
            }
            // (b'') niche int wrappers (`Nanoseconds`, ...) clone an inner primitive int -- total.
            //       The std time types (`Instant`/`SystemTime`/`Duration`) derive Clone over such
            //       a field, so without this their clone (and any holder's, e.g. a
            //       `HashMap<_, TokenBucket{ last_refill: Option<Instant> }>`) fails.
            if path.starts_with("core::num::niche_types::")
                || path.starts_with("std::num::niche_types::")
            {
                return true;
            }
            // (c) element-free std leaf (`String`/`Ordering`/`Duration`/`NonZero`).
            is_element_free_total_std_adt(tcx, did)
        }
        _ => false,
    }
}

/// True iff `<ty as TRAIT>::method` is PROVABLY panic-free (total) for an auto-derive trait
/// (`PartialEq`/`PartialOrd`/`Ord`/`Hash`/`Default`), WITHOUT an axiom. Mirrors
/// `tcx_clone_is_total`: a primitive/`str`/`!`; a raw pointer / `FnDef`/`FnPtr` (compared/
/// hashed by address, no deref); a `&T` whose referent is total (these traits dispatch INTO
/// the referent — UNLIKE clone, which copies the pointer); a tuple/array/slice of totals; an
/// ADT whose impl of `trait_did` is `#[automatically_derived]` with all field types total; a
/// std deep container of totals; or an element-free std leaf. Everything else — a hand-
/// written/foreign impl, which CAN panic — is fail-closed `false` (no false-PROVE). Fuel-
/// bounded; a cycle short-circuits to `true` (cycles arise only inside derived/container
/// chains, panic-free by construction).
fn tcx_derived_trait_is_total<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    trait_did: rustc_span::def_id::DefId,
    fuel: u32,
    seen: &mut std::collections::HashSet<ty::Ty<'tcx>>,
) -> bool {
    use rustc_middle::ty::TyKind;
    if fuel == 0 {
        return false;
    }
    if !seen.insert(ty) {
        return true;
    }
    // Non-monomorphic types (type/const params) must not reach a fully-monomorphized resolve;
    // fail closed rather than ICE (see `tcx_clone_is_total`).
    if ty.has_non_region_param() {
        return false;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never => true,
        TyKind::RawPtr(..) | TyKind::FnPtr(..) | TyKind::FnDef(..) => true,
        // These traits dispatch INTO a `&T`'s referent (unlike Clone, which copies it).
        TyKind::Ref(_, inner, _) => {
            tcx_derived_trait_is_total(tcx, *inner, trait_did, fuel - 1, seen)
        }
        TyKind::Tuple(elems) => {
            elems.iter().all(|e| tcx_derived_trait_is_total(tcx, e, trait_did, fuel - 1, seen))
        }
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            tcx_derived_trait_is_total(tcx, *elem, trait_did, fuel - 1, seen)
        }
        // A pattern type (`pattern_type!(u32 is 0..=N)`) is a range-constrained primitive whose
        // eq/hash/cmp/default are the base int's -- total iff the base is.
        TyKind::Pat(base, _) => tcx_derived_trait_is_total(tcx, *base, trait_did, fuel - 1, seen),
        TyKind::Adt(def, args) => {
            let mut derived = false;
            tcx.for_each_relevant_impl(trait_did, ty, |impl_did| {
                if tcx.is_automatically_derived(impl_did) {
                    derived = true;
                }
            });
            if derived {
                return def.all_fields().all(|f| {
                    tcx_derived_trait_is_total(
                        tcx,
                        f.ty(tcx, args).skip_normalization(),
                        trait_did,
                        fuel - 1,
                        seen,
                    )
                });
            }
            if is_std_deep_clone_container(tcx, def.did()) {
                // Recurse only the PARTICIPATING type args (the elements). A std container's
                // `eq`/`hash`/`cmp` never touches its phantom allocator (`Global`) or hasher
                // (`RandomState`) arg — which don't even impl the trait — so SKIP an arg with no
                // relevant impl of `trait_did`. (A real element arg DOES impl the trait and is
                // recursed; this matters because, unlike Clone, e.g. `Global` is `Clone` but not
                // `PartialEq`, so the un-skipped recursion would wrongly fail on it.)
                return args.types().all(|t| {
                    let mut participates = false;
                    tcx.for_each_relevant_impl(trait_did, t, |_| participates = true);
                    !participates || tcx_derived_trait_is_total(tcx, t, trait_did, fuel - 1, seen)
                });
            }
            // HashMap<K,V,_> / HashSet<K,_>: unlike BTreeMap (ordered, compares via `Ord`), the
            // wrapper's `eq` LOOKS UP keys — it calls `K::hash` AND `K::eq` — so it is total
            // only if K's Hash is also total (a subtlety the deep-clone-container arm above
            // would MISS, since that arm only recurses under the current trait). Sound,
            // conservative handling for `PartialEq`: require K to be a primitive / `str` /
            // element-free std leaf (`String`/...), whose Hash AND Eq are both total, and (for
            // HashMap) recurse the value under PartialEq. Fail-closed for an exotic key or any
            // other trait (HashMap doesn't impl Hash; under Default it is trivially empty, not
            // modeled here).
            let path = crate::safe_def_path_str(tcx, def.did());
            let leaf = path.rsplit("::").next().unwrap_or(&path);
            let leaf = leaf.split('<').next().unwrap_or(leaf);
            // Phantom/marker ZSTs — the allocator (`Global`), hasher (`RandomState`), and
            // `PhantomData` — carry no comparable/hashable data and are never touched by the
            // `eq`/`hash`/`cmp`/`default` of the std type that holds them. Treat as total
            // WHEREVER recursed (a derived type's internal `Vec<u8, Global>` / `RawVec` field
            // reaches them DIRECTLY, not only via the container arm above). SOUND: none of them
            // impls these traits in a value-bearing way; the holder skips them.
            if matches!(leaf, "Global" | "RandomState" | "PhantomData")
                && (path.starts_with("std::")
                    || path.starts_with("alloc::")
                    || path.starts_with("core::"))
            {
                return true;
            }
            // `core::num::niche_types::*` (`Nanoseconds`, `U32NotAllOnes`, ...) wrap a primitive
            // int with a validity niche; their `eq`/`hash`/`cmp`/`default` are total int ops.
            // (Std types like `Duration` derive `PartialEq`/`Hash` over such a field, so without
            // this the derived `Duration` impl — and any type holding a `Duration` — fails.)
            if path.starts_with("core::num::niche_types::")
                || path.starts_with("std::num::niche_types::")
            {
                return true;
            }
            if (leaf == "HashMap" || leaf == "HashSet")
                && (path.starts_with("std::") || path.starts_with("hashbrown::"))
            {
                match tcx.item_name(trait_did).as_str() {
                    // `default()` builds an EMPTY map/set — total, no per-element work.
                    "Default" => return true,
                    // `eq` LOOKS UP keys: total iff K's Hash AND Eq are total (restrict K to a
                    // primitive / `str` / element-free std leaf, whose Hash+Eq are both total)
                    // and (HashMap) V's Eq is total.
                    "PartialEq" => {
                        let mut tys = args.types();
                        let key_total_hash_and_eq = tys.next().is_some_and(|k| {
                            matches!(
                                k.kind(),
                                TyKind::Bool
                                    | TyKind::Char
                                    | TyKind::Int(_)
                                    | TyKind::Uint(_)
                                    | TyKind::Str
                            ) || matches!(k.kind(), TyKind::Adt(d, _)
                                if is_element_free_total_std_adt(tcx, d.did()))
                        });
                        let value_total = if leaf == "HashMap" {
                            tys.next().is_some_and(|v| {
                                tcx_derived_trait_is_total(tcx, v, trait_did, fuel - 1, seen)
                            })
                        } else {
                            true
                        };
                        return key_total_hash_and_eq && value_total;
                    }
                    // HashMap/HashSet impl neither `Hash` nor `Ord`; fail closed for anything else.
                    _ => {}
                }
            }
            is_element_free_total_std_adt(tcx, def.did())
        }
        _ => false,
    }
}

/// Derived syntax and a trait item name are not proof capabilities. Preserve
/// the real call edge until builtin-derive provenance and every callback/
/// hasher/formatter/drop effect are authenticated structurally.
pub fn is_total_derived_trait_call<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _callee_def_id: rustc_span::def_id::DefId,
    _gen_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    false
}

/// True iff the call is an `Iterator::collect::<C>` into a KEYED std collection
/// (`BTreeMap`/`BTreeSet`/`HashMap`/`HashSet`) whose KEY type's ordering/hashing impls are
/// themselves PROVABLY total — so the collect carries ZERO panic obligations.
///
/// WHY THIS IS NEEDED. The bridge's `total_sequence_collect_call` models a collect into a
/// SEQUENCE (`Vec`/`VecDeque`/`String`) as total, but deliberately EXCLUDES the keyed
/// collections, on the grounds that — unlike a `Vec` push — a keyed insert dispatches through
/// `K::cmp` (BTree) or `K::hash`/`K::eq` (Hash), which is USER code and can panic. That
/// exclusion is SOUND but strictly conservative: when `K` is a primitive, `&str`, `String`,
/// `char`, or a `#[derive]` over total fields, the user code it fears is provably panic-free,
/// and the collect's only residual failure mode is allocation abort — already outside the
/// modeled panic set, exactly as for the sequence collect it is a twin of.
///
/// Without this, EVERY `.collect::<BTreeMap<_, _>>()` mints an unbounded
/// `trust-absent-callee-assumption ... may panic UNKNOWN` row, which — because a crate's
/// verification aborts at its first unproved function — masks the entire remainder of the
/// crate behind it. The only recourse was to `#[trust::skip]` the enclosing function, which
/// discards every OTHER (real, provable) arithmetic and bounds obligation in that body too.
/// This discharges the collect instead, and lets those obligations back into the denominator.
///
/// SOUNDNESS. The sentinel is emitted ONLY when `tcx_derived_trait_is_total` certifies EVERY
/// trait the insert path can dispatch through: `Ord` for the BTree family (its `cmp` drives the
/// tree descent), `Hash` + `Eq` for the Hash family (hash to bucket, eq to resolve collision).
/// That predicate is the SAME fail-closed one behind the derived-trait sentinel: it requires
/// `#[automatically_derived]` at every recursion level and returns `false` for a hand-written or
/// foreign impl, an un-monomorphized param, or a panic-capable field — in which case the collect
/// KEEPS its obligation and the caller is refuted as before (no false-PROVE).
///
/// Three further fail-closed gates, each guarding a way the discharge could otherwise be wrong:
///   - the DESTINATION must be defined in `core`/`alloc`/`std`, so a user collection that merely
///     NAMES itself `BTreeMap` is not admitted (mirrors `total_sequence_collect_call`);
///   - the destination must be MONOMORPHIC (`has_non_region_param`), so we never resolve into a
///     param-env ICE (the `tcx_clone_is_total` precedent);
///   - for the Hash family, the HASHER `S` must itself be a std type. `S` is a type parameter
///     defaulting to `RandomState`, so a caller CAN supply a hand-written `BuildHasher`/`Hasher`
///     whose `write`/`finish` is user code that can panic; only std's own hasher is inside the
///     trusted `Hasher` surface. A foreign hasher fails closed.
///
/// NOTE what is deliberately NOT claimed: this says nothing about ALLOCATION. A keyed collect can
/// still abort on OOM, exactly as its sequence twin can, and that abort stays outside the modeled
/// panic set for both. It is NOT a licence to wave through a size-driven allocation panic (e.g.
/// `Vec::with_capacity(untrusted_len)`), which remains a real, refutable obligation.
fn is_total_keyed_collect_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: rustc_span::def_id::DefId,
    gen_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    use rustc_span::sym;

    // Pin to `Iterator::collect`. Resolve through the impl to the trait method so both the
    // monomorphized `<I as Iterator>::collect::<C>` and the bare spelling land here.
    if tcx.item_name(callee_def_id).as_str() != "collect" {
        return false;
    }
    let trait_did = tcx.trait_of_assoc(callee_def_id).or_else(|| {
        tcx.trait_impl_of_assoc(callee_def_id).map(|impl_did| {
            tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization().def_id
        })
    });
    match trait_did {
        Some(t) if tcx.is_diagnostic_item(sym::Iterator, t) => {}
        _ => return false,
    }

    // `<I as Iterator>::collect::<C>` — args are [Self = I, C]. `C` is the destination.
    let Some(dest_ty) = gen_args.types().nth(1) else {
        return false;
    };
    // Fail closed on a non-monomorphized destination rather than resolve into a param-env ICE
    // (the `tcx_clone_is_total` precedent).
    if dest_ty.has_non_region_param() {
        return false;
    }
    let ty::Adt(def, args) = dest_ty.kind() else {
        return false;
    };

    // Destination must be one of the four std keyed collections. Match on the ADT's item name
    // plus its DEFINING CRATE — not a `def_path_str` substring, whose real spelling is the
    // internal `alloc::collections::btree::map::BTreeMap`. The crate gate keeps a like-named
    // USER collection out (mirroring `total_sequence_collect_call`'s origin gate).
    let adt_name = tcx.item_name(def.did());
    let keyed_by_ord = matches!(adt_name.as_str(), "BTreeMap" | "BTreeSet");
    let keyed_by_hash = matches!(adt_name.as_str(), "HashMap" | "HashSet");
    if !(keyed_by_ord || keyed_by_hash) {
        return false;
    }
    let krate = tcx.crate_name(def.did().krate);
    if !matches!(krate.as_str(), "core" | "alloc" | "std") {
        return false;
    }

    // In all four (`BTreeMap<K, V, A>`, `BTreeSet<T, A>`, `HashMap<K, V, S>`, `HashSet<T, S>`)
    // the KEY is the first type argument. The VALUE is never compared or hashed on insert, so
    // its impls are irrelevant here.
    let Some(key_ty) = args.types().next() else {
        return false;
    };

    let total_for = |item: rustc_span::Symbol| {
        tcx.get_diagnostic_item(item).is_some_and(|trait_did| {
            tcx_derived_trait_is_total(
                tcx,
                key_ty,
                trait_did,
                CLONE_TOTALITY_FUEL,
                &mut std::collections::HashSet::new(),
            )
        })
    };

    if keyed_by_ord {
        // BTree descent compares keys via `Ord::cmp`.
        return total_for(sym::Ord);
    }

    // Hash family. The bucket index comes from `Hash::hash` feeding the collection's HASHER `S`,
    // and a collision is resolved by `Eq`. `S` is a TYPE PARAMETER (`HashMap<K, V, S>` /
    // `HashSet<T, S>`, both defaulting to std's `RandomState`), so a caller can supply a
    // hand-written `BuildHasher`/`Hasher` whose `write`/`finish` is USER code and CAN panic.
    // Only std's own hasher is inside the trusted `Hasher` surface, so require `S` to come from
    // std; a foreign hasher fails closed and the collect keeps its obligation.
    let hasher_ty =
        if adt_name.as_str() == "HashMap" { args.types().nth(2) } else { args.types().nth(1) };
    let Some(hasher_ty) = hasher_ty else {
        return false;
    };
    let ty::Adt(hasher_def, _) = hasher_ty.kind() else {
        return false;
    };
    if !matches!(tcx.crate_name(hasher_def.did().krate).as_str(), "core" | "alloc" | "std") {
        return false;
    }

    total_for(sym::Hash) && total_for(sym::Eq)
}

/// True iff the call is `<C as Extend<T>>::extend` (or the bare `Extend::extend`) whose RECEIVER
/// collection `C` is a std collection that inserts panic-free: a KEYED collection
/// (`BTreeMap`/`BTreeSet`/`HashMap`/`HashSet`) with a total-`Ord`/`Hash`+`Eq` key (same gate as
/// `is_total_keyed_collect_call`, applied to `C` = Self instead of the collect destination), or a
/// SEQUENCE collection (`Vec`/`VecDeque`/`String`) whose push runs no user comparison at all.
///
/// The extend-twin of the collect/insert discharge: `extend` pulls items from the (separately-
/// verified) source iterator and inserts each, so — given a total key and a std hasher for the
/// Hash family — it runs no panicking user code and its only residual failure is allocation abort
/// (outside the modeled panic set). A user key with a panicking `Ord`/`Hash`, a non-std hasher, or
/// a non-std / non-monomorphic receiver fails the gate and KEEPS its obligation (no false-PROVE).
fn is_total_collection_extend_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: rustc_span::def_id::DefId,
    gen_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    use rustc_span::sym;
    if tcx.item_name(callee_def_id).as_str() != "extend" {
        return false;
    }
    let trait_did = tcx.trait_of_assoc(callee_def_id).or_else(|| {
        tcx.trait_impl_of_assoc(callee_def_id).map(|impl_did| {
            tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization().def_id
        })
    });
    // `Extend` is a std trait but not a diagnostic item; match by name + std origin.
    match trait_did {
        Some(t)
            if tcx.item_name(t).as_str() == "Extend" && {
                let k = tcx.crate_name(t.krate);
                matches!(k.as_str(), "core" | "alloc" | "std")
            } => {}
        _ => return false,
    }
    // `<C as Extend<T>>::extend` — Self (the collection `C`) is the first type arg.
    let Some(self_ty) = gen_args.types().next() else {
        return false;
    };
    if self_ty.has_non_region_param() {
        return false;
    }
    let ty::Adt(def, args) = self_ty.kind() else {
        return false;
    };
    let adt_name = tcx.item_name(def.did());
    if !matches!(tcx.crate_name(def.did().krate).as_str(), "core" | "alloc" | "std") {
        return false;
    }
    // Sequence collections: push runs no user comparison — total for any element.
    if matches!(adt_name.as_str(), "Vec" | "VecDeque" | "String") {
        return true;
    }
    let keyed_by_ord = matches!(adt_name.as_str(), "BTreeMap" | "BTreeSet");
    let keyed_by_hash = matches!(adt_name.as_str(), "HashMap" | "HashSet");
    if !(keyed_by_ord || keyed_by_hash) {
        return false;
    }
    let Some(key_ty) = args.types().next() else {
        return false;
    };
    let total_for = |item: rustc_span::Symbol| {
        tcx.get_diagnostic_item(item).is_some_and(|trait_did| {
            tcx_derived_trait_is_total(
                tcx,
                key_ty,
                trait_did,
                CLONE_TOTALITY_FUEL,
                &mut std::collections::HashSet::new(),
            )
        })
    };
    if keyed_by_ord {
        return total_for(sym::Ord);
    }
    // Hash family: gate on a std hasher `S`, exactly like the collect twin.
    let hasher_ty =
        if adt_name.as_str() == "HashMap" { args.types().nth(2) } else { args.types().nth(1) };
    let Some(hasher_ty) = hasher_ty else { return false };
    let ty::Adt(hasher_def, _) = hasher_ty.kind() else { return false };
    if !matches!(tcx.crate_name(hasher_def.did().krate).as_str(), "core" | "alloc" | "std") {
        return false;
    }
    total_for(sym::Hash) && total_for(sym::Eq)
}

/// True iff the call is an inherent `HashMap`/`HashSet` query method (`get`/`get_mut`/`remove`/
/// `contains_key`/`contains`/`insert`/`take`/`get_key_value`/`remove_entry`) whose KEY is total
/// (`Hash` + `Eq` derived over total fields) AND whose HASHER `S` is a std type — so the hash +
/// bucket probe + collision `Eq` run no panicking user code (only allocation abort remains, out of
/// the modeled panic set). The Hash-family twin of the BTreeMap-read discharge
/// (`is_std_ord_key_map_insert_absent_callee`, which needs no hasher gate). SOUND: `S` is a type
/// parameter (`HashMap<K,V,S>` defaults to std `RandomState`), so a caller can supply a
/// hand-written `BuildHasher`/`Hasher` whose `write`/`finish` panics — REQUIRE `S` from std; a
/// user key with a panicking `Hash`/`Eq`, a non-std hasher, or a non-std/non-monomorphic receiver
/// fails the gate and KEEPS its obligation. `range`-like ordered ops don't exist on Hash tables.
fn is_total_hash_map_query_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    method_def_id: rustc_span::def_id::DefId,
    gen_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    use rustc_hir::def::DefKind;
    use rustc_span::sym;
    if !matches!(
        tcx.item_name(method_def_id).as_str(),
        "get"
            | "get_mut"
            | "remove"
            | "contains_key"
            | "contains"
            | "insert"
            | "take"
            | "get_key_value"
            | "remove_entry"
    ) {
        return false;
    }
    let impl_did = tcx.parent(method_def_id);
    if !matches!(tcx.def_kind(impl_did), DefKind::Impl { of_trait: false }) {
        return false;
    }
    let self_ty = tcx.type_of(impl_did).instantiate(tcx, gen_args).skip_normalization();
    if self_ty.has_non_region_param() {
        return false;
    }
    let ty::TyKind::Adt(def, args) = self_ty.kind() else {
        return false;
    };
    let is_map = tcx.item_name(def.did()).as_str() == "HashMap";
    let is_set = tcx.item_name(def.did()).as_str() == "HashSet";
    if !(is_map || is_set) {
        return false;
    }
    if !matches!(tcx.crate_name(def.did().krate).as_str(), "core" | "alloc" | "std") {
        return false;
    }
    let Some(key_ty) = args.types().next() else {
        return false;
    };
    // Hasher `S`: HashMap<K,V,S> -> nth(2); HashSet<T,S> -> nth(1). Must be std.
    let hasher_ty = if is_map { args.types().nth(2) } else { args.types().nth(1) };
    let Some(hasher_ty) = hasher_ty else {
        return false;
    };
    let ty::TyKind::Adt(hasher_def, _) = hasher_ty.kind() else {
        return false;
    };
    if !matches!(tcx.crate_name(hasher_def.did().krate).as_str(), "core" | "alloc" | "std") {
        return false;
    }
    let total_for = |item: rustc_span::Symbol| {
        tcx.get_diagnostic_item(item).is_some_and(|trait_did| {
            tcx_derived_trait_is_total(
                tcx,
                key_ty,
                trait_did,
                CLONE_TOTALITY_FUEL,
                &mut std::collections::HashSet::new(),
            )
        })
    };
    total_for(sym::Hash) && total_for(sym::Eq)
}

/// Never replace a derived method body with synthetic zero-obligation evidence.
/// `#[automatically_derived]` is source-spellable and does not authenticate a
/// builtin expansion; Hash/Debug also execute caller-provided hasher/writer
/// behavior. The real MIR remains the only current authority.
pub fn is_derived_total_method(_tcx: TyCtxt<'_>, _def_id: rustc_span::def_id::DefId) -> bool {
    false
}

/// Convert a rustc Terminator to our Terminator.
fn convert_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &mir::Terminator<'tcx>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Terminator {
    // Trust: extract per-terminator source span for diagnostics
    let span = convert_span(tcx, terminator.source_info.span);
    match &terminator.kind {
        mir::TerminatorKind::Goto { target } => Terminator::Goto(BlockId(target.as_usize())),
        mir::TerminatorKind::SwitchInt { discr, targets } => {
            let switch_targets: Vec<(u128, BlockId)> =
                targets.iter().map(|(val, bb)| (val, BlockId(bb.as_usize()))).collect();
            let otherwise = BlockId(targets.otherwise().as_usize());

            Terminator::SwitchInt {
                discr: convert_operand(tcx, discr, typing_env),
                targets: switch_targets,
                otherwise,
                // Sound default: the TyCtxt-vetted exhaustiveness determination
                // is stamped in a post-pass (`mark_exhaustive_enum_unreachable_switches`)
                // that has the full `mir::Body` + lowered locals; this arm sees
                // only `(tcx, &terminator)` and cannot decide it here.
                exhaustive_enum_unreachable: false,
                span, // Trust: per-terminator source span
            }
        }
        mir::TerminatorKind::Return => Terminator::Return,
        mir::TerminatorKind::Unreachable => Terminator::Unreachable,
        mir::TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
            // Preserve the exact rendered call key used by both extraction and
            // summary registration. The former Clone/derived sentinel rewrite is
            // gone: a source-spellable attribute cannot mint totality.
            let func_name = func_operand_name(tcx, func);
            let successors: Vec<BlockId> =
                terminator.kind.successors().map(|bb| BlockId(bb.as_usize())).collect();
            let normal_targets: Vec<BlockId> =
                target.iter().map(|bb| BlockId(bb.as_usize())).collect();
            // FAITHFUL UNWIND MODELING: record the Call's unwind/cleanup edge as a
            // real CFG successor (`unwind: convert_unwind_action(*unwind)` on the
            // constructed `Terminator::Call` below) and route the normal-return path
            // to `target` as before. A `Cleanup(bb)` edge keeps the cleanup block
            // reachable so the verifier traverses it and proves its live-local drops
            // panic-free (before this, the edge was dropped, the cleanup block was
            // pruned, and its drops went unchecked — a gap the drop-glue analysis was
            // relied on to cover; now they are checked directly).
            //
            // SOUNDNESS: recording the edge as an (unguarded, always-explored)
            // successor is a SOUND over-approximation — the verifier checks the
            // cleanup drops on MORE paths than reality, never fewer. It never lets a
            // cleanup-path panic be reported as Proved: each cleanup-block `Drop`
            // keeps its ordinary drop-glue panic-freedom obligation (undischarged =>
            // unknown) exactly like a normal-path drop. Independently, a Call's unwind
            // edge is TAKEN only if the callee panics, and that hazard already has its
            // own obligation (the callee's own verification, or the bridge's
            // `trust-absent-callee-assumption` may-panic obligation for an absent
            // callee, keyed on callee RESOLUTION) — so recording the edge adds
            // reachability, never masks an obligation. (Indirect calls and diverging
            // calls without a normal-return target still fail closed / are handled by
            // the explicit sinks below.)

            // A direct nounwind call with a normal-return target can be represented
            // exactly by TrustIr. Indirect and diverging calls remain fail-closed,
            // except for the explicitly modeled sinks below.
            // A diverging call to a PANIC function (`core::panicking::panic`,
            // `panic_fmt`, `panic_bounds_check`, …) is the canonical
            // `assert!`/explicit-panic pattern: rustc lowers `if !cond { panic }`
            // to a SwitchInt whose panic arm is a diverging call. Emit it as a
            // `Call` (target stays None) so the bridge's panic path fires —
            // `assert(false)` under the current path condition + a PanicFreedom
            // obligation, i.e. "this panic point must be proven unreachable".
            // Sound: a genuinely reachable panic yields a satisfiable path
            // condition and is correctly NOT proved; an unreachable one
            // discharges vacuously. Without this the panic arm stayed `Opaque`,
            // the whole function failed to lower, and every user `assert!`
            // fell closed to Unknown. Indirect calls and NON-panic diverging
            // calls still stay opaque / fail-closed.
            let is_diverging_panic = target.is_none()
                && func_name != "<indirect>"
                && is_panic_diverging_call(&func_name);
            // Trust: a DIRECT call to a recognized bulk-allocation / collect sink
            // (`with_capacity`/`reserve`/`resize`/`from_elem`/`collect`/`from_iter`)
            // whose post-inlining shape has NO normal-return target (`target ==
            // None`) is otherwise swallowed by the `opaque_terminator` bail below —
            // so trust-vcgen's UnboundedAllocation recognizer never sees the size
            // argument and the nn OOM passes silently. Instead, emit a real
            // `Terminator::Call` routed to the divergence/cleanup successor sink,
            // exactly as the Drop/Resume/panic-diverging arms route control flow to
            // a no-obligation sink. SOUND by the identical argument those arms use:
            // a `Call` whose target is a divergence sink adds NO assumption and
            // removes NO normal-path obligation — it only makes the (preserved) size
            // operand reachable to the recognizer, which then either proves the
            // allocation bounded or fails it closed. Indirect calls and non-sink
            // diverging calls still fall through to the opaque bail.
            let is_direct_bulk_alloc_sink = target.is_none()
                && func_name != "<indirect>"
                && is_bulk_alloc_sink_call(&func_name);
            // Historical process-exit abstraction point. The classifier is deliberately
            // fail-closed until rustc's authenticated std DefId is carried here: a display-path
            // suffix alone cannot authorize rewriting a real diverging call to `Return`.
            if target.is_none() && func_name != "<indirect>" && is_total_noreturn_call(&func_name) {
                return Terminator::Return;
            }
            if (func_name == "<indirect>" || target.is_none())
                && !is_diverging_panic
                && !is_direct_bulk_alloc_sink
            {
                let opaque_kind = if func_name == "<indirect>" {
                    "Call(indirect)".to_string()
                } else {
                    format!("Call::{func_name}")
                };
                return opaque_terminator(opaque_kind, successors, span);
            }
            let converted_args: Vec<Operand> = args
                .iter()
                .map(|spanned| convert_operand(tcx, &spanned.node, typing_env))
                .collect();
            let dest = convert_place(tcx, destination, typing_env);

            // concurrency-coverage: detect atomic intrinsics and
            // populate metadata. If a call is recognizably atomic but its
            // ordering metadata is missing or non-concrete, fail closed as an
            // opaque terminator; otherwise vcgen would see a plain call and
            // silently skip atomic legality coverage.
            let atomic =
                match parse_atomic_intrinsic_metadata(&func_name, &converted_args, &dest, &span) {
                    AtomicIntrinsicMetadata::Parsed(op) => Some(op),
                    AtomicIntrinsicMetadata::NotAtomic => None,
                    AtomicIntrinsicMetadata::Malformed { detail } => {
                        return opaque_terminator(
                            format!("Call::{func_name}::UnsupportedAtomicMetadata({detail})"),
                            normal_targets,
                            span,
                        );
                    }
                };

            // Trust: round-19 #3 — record AUTHORITATIVE foreign-ness here.
            // trust-vcgen's name-substring detection (`is_extern_call`) misses
            // `extern { fn compute_hash(); }` imports whose path lacks
            // libc/extern/ffi, so the FFI boundary obligation was never emitted
            // and the caller could be reported Proved over an unchecked foreign
            // boundary. `is_foreign` propagates the real signal; trust-vcgen
            // treats it as definitive (name-substring stays a fallback). Paired
            // with round-19 #4 (unmodeled FFI fails closed), this closes the
            // foreign-boundary over-claim end to end.
            // `core::mem::drop(x)` — the identity-to-drop fn: its ENTIRE
            // semantics is "run x's drop glue here". Lower it AS a `Drop`
            // terminator so the existing drop-glue machinery (structural-drop
            // facts, the audited std-Drop list) judges the glue directly,
            // instead of minting an absent-callee row for the trivial std fn
            // body. Only the exact std/core path with ONE whole-place by-value
            // argument rewrites; every other shape keeps the plain Call
            // (fail-closed).
            if matches!(func_name.as_str(), "std::mem::drop" | "core::mem::drop") {
                if let ([Operand::Move(p) | Operand::Copy(p)], Some(t)) =
                    (converted_args.as_slice(), target)
                {
                    if p.projections.is_empty() {
                        return Terminator::Drop {
                            place: p.clone(),
                            target: BlockId(t.as_usize()),
                            span,
                            // Trust: the rewritten Drop keeps the Call's own
                            // unwind/cleanup edge — the glue-panic path is the
                            // same control flow either way (see
                            // `convert_unwind_action`; faithful, never masking).
                            unwind: convert_unwind_action(*unwind),
                        };
                    }
                }
            }
            Terminator::Call {
                func: func_name,
                args: converted_args,
                dest,
                target: target.map(|bb| BlockId(bb.as_usize())),
                span, // Trust: per-terminator source span
                atomic,
                is_foreign: func_operand_is_foreign(tcx, func),
                // Trust: T5A — record the AUTHORITATIVE unsafe-signature signal
                // here (tcx.fn_sig safety, target_feature-gated) so trust-vcgen's
                // unsafe-block detection no longer needs the `::ffi::` NAMESPACE
                // name heuristic that falsely demanded SAFETY comments on safe
                // std::ffi paths (OsStr::to_str & friends).
                is_unsafe_sig: func_operand_is_unsafe_sig(tcx, func),
                // Faithfully record the cleanup/unwind successor (see comment
                // above): a `Cleanup(bb)` edge keeps the cleanup block reachable so
                // its live-local drops are verified; a sound over-approximation that
                // never masks an obligation.
                unwind: convert_unwind_action(*unwind),
            }
        }
        // Trust: CRITICAL — Assert terminators encode rustc's overflow checks,
        // bounds checks, and div-by-zero checks.
        //
        // FAITHFUL UNWIND MODELING: record the Assert's unwind/cleanup edge as a
        // real CFG successor (`unwind: convert_unwind_action(*unwind)` below) and
        // route the success path to `target` as before. An Assert's unwind edge is
        // TAKEN only when the assert FAILS — exactly the panic the verifier is
        // proving unreachable — and the success-path obligation (`cond == expected`,
        // e.g. no overflow) fully captures the safety property, so recording the
        // edge adds no assert-specific obligation. But a `Cleanup(bb)` assert edge
        // still transfers to a real cleanup block that drops the live locals, so we
        // record it (rather than drop it) to keep that block reachable and prove its
        // drops panic-free. SOUNDNESS: an always-explored cleanup successor over-
        // approximates (checks drops on more paths, never fewer) and never masks the
        // success-path obligation.
        mir::TerminatorKind::Assert { cond, expected, msg, target, unwind, .. } => {
            let msg = match convert_assert_message(msg) {
                Ok(msg) => msg,
                Err(detail) => {
                    let successors: Vec<BlockId> =
                        terminator.kind.successors().map(|bb| BlockId(bb.as_usize())).collect();
                    return opaque_terminator(format!("Assert::{detail}"), successors, span);
                }
            };
            Terminator::Assert {
                cond: convert_operand(tcx, cond, typing_env),
                expected: *expected,
                msg,
                target: BlockId(target.as_usize()),
                span, // Trust: per-terminator source span
                unwind: convert_unwind_action(*unwind),
            }
        }
        // FAITHFUL UNWIND MODELING (the KEY fix — this was the dominant ny-cert
        // frontier: every owned-value-holding function hit `Drop::UnsupportedUnwind`
        // and wedged at Opaque). Record the Drop's unwind/cleanup edge as a real CFG
        // successor instead of fail-closing on it. A Drop's unwind edge is the
        // panic-DURING-drop path: when this drop's glue panics, control transfers to
        // the `Cleanup(bb)` block, which drops the remaining live locals via its own
        // `Drop` terminators and ends in `UnwindResume` (`Terminator::Resume`). By
        // recording the edge, the verifier TRAVERSES that cleanup block and proves
        // each of its drops panic-free.
        //
        // SOUNDNESS: this drop's OWN drop-glue panic-freedom obligation is emitted by
        // the bridge for the `Terminator::Drop` itself (independent of the unwind
        // edge); the cleanup block's drops likewise each keep their own obligation.
        // Recording the cleanup edge as an always-explored successor is a sound
        // over-approximation (checks the cleanup drops on more paths than reality,
        // never fewer) and never lets a cleanup-path drop panic be reported as Proved
        // — an unproven cleanup drop stays an undischarged (unknown) obligation, just
        // like a normal-path drop.
        mir::TerminatorKind::Drop { place, target, unwind, .. } => Terminator::Drop {
            place: convert_place(tcx, place, typing_env),
            target: BlockId(target.as_usize()),
            span, // Trust: per-terminator source span
            unwind: convert_unwind_action(*unwind),
        },
        mir::TerminatorKind::FalseEdge { real_target, .. } => {
            Terminator::Goto(BlockId(real_target.as_usize()))
        }
        mir::TerminatorKind::FalseUnwind { real_target, .. } => {
            Terminator::Goto(BlockId(real_target.as_usize()))
        }
        mir::TerminatorKind::CoroutineDrop => Terminator::Return,
        // `UnwindResume` re-raises an in-flight unwind to the caller.
        // Lower it to a dedicated no-obligation divergence sink instead of the
        // `Opaque` catch-all (which wedged every cleanup-carrying function at
        // Unknown). NOT `Unreachable`: cleanup blocks are reachable while a panic
        // is in flight, so an assert-unreachable here would be a false failure.
        mir::TerminatorKind::UnwindResume => Terminator::Resume,
        // `UnwindTerminate` aborts rather than propagating an unwind. Mapping it
        // to `Resume` loses that distinction and can hide a reachable panic at a
        // non-unwind boundary. TrustIr has no terminate sink yet, so fail closed.
        mir::TerminatorKind::UnwindTerminate(reason) => {
            opaque_terminator(format!("UnwindTerminate::{reason:?}"), vec![], span)
        }
        _ => opaque_terminator(
            terminator.kind.name(),
            terminator.kind.successors().map(|bb| BlockId(bb.as_usize())).collect(),
            span,
        ),
    }
}

/// Faithfully convert a rustc `mir::UnwindAction` to a TrustIr `UnwindEdge`.
///
/// This RECORDS the cleanup/unwind successor rather than fail-closing on it (the
/// former `unsupported_unwind_action` behavior). Modeling the edge is what lets
/// the verifier TRAVERSE the cleanup block referenced by `Cleanup(bb)` — which
/// drops the function's live locals via its own `Drop` terminators and ends in
/// `UnwindResume` (`Terminator::Resume`) — and prove each cleanup-path drop
/// panic-free, instead of pruning the block as dead (which would hide a
/// cleanup-path panic) or wedging the whole terminator at `Opaque` (which
/// needlessly blocked `Proved` for every owned-value-holding function).
///
/// SOUNDNESS: recording the edge adds a CFG successor that is always explored,
/// so the cleanup drops are checked on MORE paths than reality, never fewer.
/// Each cleanup-block `Drop` keeps its ordinary drop-glue panic-freedom
/// obligation (see the Drop arm / trust-ir-bridge); nothing here discharges or
/// skips those obligations.
fn convert_unwind_action(action: mir::UnwindAction) -> UnwindEdge {
    match action {
        mir::UnwindAction::Unreachable => UnwindEdge::Unreachable,
        mir::UnwindAction::Continue => UnwindEdge::Continue,
        mir::UnwindAction::Terminate(_) => UnwindEdge::Terminate,
        mir::UnwindAction::Cleanup(bb) => UnwindEdge::Cleanup(BlockId(bb.as_usize())),
    }
}

fn opaque_terminator(
    kind: impl Into<String>,
    targets: Vec<BlockId>,
    span: SourceSpan,
) -> Terminator {
    Terminator::Opaque { kind: kind.into(), targets: dedupe_block_ids(targets), span }
}

/// Whether a (diverging) call target is a panic-emitting runtime function.
///
/// Kept deliberately in lockstep with `is_panic_call` in
/// `trust-ir-bridge/src/lower.rs`: the bridge only lowers a `Call` to the
/// panic-freedom shape (`assert(false)` under the path condition) for callees
/// matching that predicate, so a diverging call routed to `Call` here must be
/// recognized there too — otherwise it would fail closed at the bridge instead
/// of staying Opaque here.
fn is_panic_diverging_call(callee: &str) -> bool {
    callee.contains("::panicking::")
        || callee.contains("begin_panic")
        || callee.ends_with("::panic")
        || callee.ends_with("::panic_fmt")
        || callee.ends_with("::panic_nounwind")
        || callee.contains("panic_bounds_check")
        || callee.contains("panic_misaligned_pointer_dereference")
        || callee.contains("panic_cannot_unwind")
}

/// No string-only diverging-call identity can authorize a path-ending rewrite.
///
/// `std::process::exit` is total and non-returning, but the rendered callee path is not an
/// authenticated std identity. Preserve it as opaque until the exact compiler-owned DefId is
/// carried through this boundary; a user same-tail function must not erase its body or effects.
pub(crate) fn is_total_noreturn_call(callee: &str) -> bool {
    let _ = callee;
    // A display-path suffix is forgeable by a user `my::process::exit -> !`.
    // Re-enable only with the exact compiler-authenticated std DefId.
    false
}

/// A diverging call to the GLOBAL ALLOCATION-FAILURE handler: on OOM the process ABORTS.
/// This is NOT a panic — no unwind runs, `catch_unwind` never observes it, the
/// `#[panic_handler]` is not invoked, and no user code executes. So, like `process::exit`
/// (`is_total_noreturn_call`), the call carries NO panic obligation and is modeled as a
/// path-ending `Return`: the code LEADING to the allocation keeps every obligation, and the
/// genuinely-unreachable OOM continuation is simply not explored.
///
/// SOUNDNESS vs `is_total_noreturn_call`'s deliberate exclusion of `abort`: that predicate
/// excludes `process::abort`/`intrinsics::abort` as a CATEGORY because under `panic = "abort"`
/// a PANIC lowers to an abort, so excusing "abort" wholesale could mask a panic. This predicate
/// excuses no category — it names the specific ALLOC-ERROR-HANDLER SYMBOLS. A `panic!` never
/// lowers to `handle_alloc_error`: it routes through `core::panicking::*` → `rust_begin_unwind`
/// and is caught by `is_panic_diverging_call`. And the genuine capacity-overflow PANIC
/// (`alloc::raw_vec::capacity_overflow` → `panic!("capacity overflow")`) is likewise a panic
/// symbol, NOT an alloc-error-handler, so it stays a real obligation. The separate vcgen
/// `UnboundedAllocation` lane still sees the preserved `with_capacity`/`collect` size operand.
///
/// STD-ORIGIN GATE: a user fn merely named `handle_alloc_error` in a non-std crate cannot enter
/// this class (mirrors the origin gates on the totality sentinels).
fn is_alloc_failure_abort_call(callee: &str) -> bool {
    let std_origin = callee.starts_with("alloc::")
        || callee.starts_with("std::")
        || callee.starts_with("core::");
    if !std_origin {
        return false;
    }
    callee.ends_with("::handle_alloc_error")
        || callee.ends_with("::__rust_alloc_error_handler")
        || callee.ends_with("::__rdl_oom")
}

// Trust: tail-match a DIRECT call to a recognized bulk-allocation / collect
// sink. Mirrors trust-vcgen's `bulk_alloc_call` + `is_collect_sink` recognizers
// (with_capacity/reserve/resize/from_elem + collect/from_iter) so that a
// no-normal-target call to one of these is NOT swallowed by the opaque bail —
// it is instead emitted as a real `Terminator::Call` whose size argument the
// vcgen UnboundedAllocation recognizer can then see. Strip generic noise from
// the method tail exactly as the recognizers do.
fn is_bulk_alloc_sink_call(callee: &str) -> bool {
    let tail = callee.rsplit("::").next().unwrap_or(callee);
    let tail = tail.split('<').next().unwrap_or(tail).trim();
    matches!(
        tail,
        "with_capacity"
            | "with_capacity_in"
            | "reserve"
            | "reserve_exact"
            | "resize"
            | "resize_with"
            | "from_elem"
            | "collect"
            | "from_iter"
    )
}

fn dedupe_block_ids(targets: Vec<BlockId>) -> Vec<BlockId> {
    let mut deduped = Vec::with_capacity(targets.len());
    for target in targets {
        if !deduped.contains(&target) {
            deduped.push(target);
        }
    }
    deduped
}

// Atomic intrinsic detection
// ---------------------------------------------------------------------------

/// Parse a MIR function call name to detect atomic intrinsics.
///
/// Handles two forms of atomic intrinsic calls in optimized MIR:
///
/// **Form A** (suffix-encoded ordering):
///   `core::intrinsics::atomic_load_seqcst(ptr)`
///   `core::intrinsics::atomic_cxchg_acqrel_acquire(ptr, old, new)`
///
/// **Form B** (generic atomic calls with explicit Ordering argument):
///   `atomic::atomic_load::<usize>(ptr, Ordering::Acquire)`
///
/// Returns `Some(AtomicOperation)` if the call is a recognized atomic intrinsic,
/// `None` otherwise.
#[cfg(test)]
pub(crate) fn parse_atomic_intrinsic(
    func_name: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    match parse_atomic_intrinsic_metadata(func_name, args, dest, span) {
        AtomicIntrinsicMetadata::Parsed(op) => Some(op),
        AtomicIntrinsicMetadata::Malformed { .. } | AtomicIntrinsicMetadata::NotAtomic => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AtomicIntrinsicMetadata {
    Parsed(AtomicOperation),
    Malformed { detail: String },
    NotAtomic,
}

fn parse_atomic_intrinsic_metadata(
    func_name: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> AtomicIntrinsicMetadata {
    // Form A: core::intrinsics::atomic_*
    if let Some(suffix) = func_name.strip_prefix("core::intrinsics::atomic_") {
        return parse_form_a(suffix, args, dest, span)
            .map(AtomicIntrinsicMetadata::Parsed)
            .unwrap_or_else(|| AtomicIntrinsicMetadata::Malformed {
                detail: format!("unrecognized or malformed intrinsic suffix `{suffix}`"),
            });
    }

    // Form B: contains "atomic::atomic_" — generic atomic calls
    if let Some(idx) = func_name.find("atomic::atomic_") {
        let after = &func_name[idx + "atomic::atomic_".len()..];
        // Strip generic suffix like "::<usize>"
        let op_name = after.split("::").next().unwrap_or(after);
        return parse_form_b(op_name, args, dest, span);
    }

    // Also handle bare "fence" or "atomic::fence" / "compiler_fence"
    if func_name.ends_with("::fence") || func_name == "fence" {
        let Some(ordering) = ordering_from_args(args, 0) else {
            return AtomicIntrinsicMetadata::Malformed {
                detail:
                    "fence ordering argument is missing or not a concrete Ordering discriminant"
                        .to_string(),
            };
        };
        return AtomicIntrinsicMetadata::Parsed(AtomicOperation {
            place: Place::local(0),
            dest: None,
            op_kind: AtomicOpKind::Fence,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        });
    }
    if func_name.ends_with("::compiler_fence") || func_name == "compiler_fence" {
        let Some(ordering) = ordering_from_args(args, 0) else {
            return AtomicIntrinsicMetadata::Malformed {
                detail:
                    "compiler_fence ordering argument is missing or not a concrete Ordering discriminant"
                        .to_string(),
            };
        };
        return AtomicIntrinsicMetadata::Parsed(AtomicOperation {
            place: Place::local(0),
            dest: None,
            op_kind: AtomicOpKind::CompilerFence,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        });
    }

    AtomicIntrinsicMetadata::NotAtomic
}

/// Parse Form A intrinsic: the part after "core::intrinsics::atomic_".
///
/// Patterns: `load_{ordering}`, `store_{ordering}`, `cxchg_{s}_{f}`,
/// `cxchgweak_{s}_{f}`, `xchg_{ordering}`, `fence_{ordering}`,
/// `singlethreadfence_{ordering}`, `xadd_{ordering}`, `xsub_{ordering}`,
/// `and_{ordering}`, `or_{ordering}`, `xor_{ordering}`, `nand_{ordering}`,
/// `min_{ordering}`, `max_{ordering}`, `umin_{ordering}`, `umax_{ordering}`.
fn parse_form_a(
    suffix: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> Option<AtomicOperation> {
    // Try each operation prefix, longest-first to avoid ambiguity.
    let ops: &[(&str, AtomicOpKind, bool)] = &[
        ("cxchgweak_", AtomicOpKind::CompareExchangeWeak, true),
        ("cxchg_", AtomicOpKind::CompareExchange, true),
        ("singlethreadfence_", AtomicOpKind::CompilerFence, false),
        ("fence_", AtomicOpKind::Fence, false),
        ("load_", AtomicOpKind::Load, false),
        ("store_", AtomicOpKind::Store, false),
        ("xchg_", AtomicOpKind::Exchange, false),
        ("xadd_", AtomicOpKind::FetchAdd, false),
        ("xsub_", AtomicOpKind::FetchSub, false),
        ("nand_", AtomicOpKind::FetchNand, false),
        ("umin_", AtomicOpKind::FetchMin, false),
        ("umax_", AtomicOpKind::FetchMax, false),
        ("and_", AtomicOpKind::FetchAnd, false),
        ("or_", AtomicOpKind::FetchOr, false),
        ("xor_", AtomicOpKind::FetchXor, false),
        ("min_", AtomicOpKind::FetchMin, false),
        ("max_", AtomicOpKind::FetchMax, false),
    ];

    for &(prefix, op_kind, is_cas) in ops {
        if let Some(ordering_part) = suffix.strip_prefix(prefix) {
            let place = extract_place_from_args(args, op_kind);
            let has_dest = !op_kind.is_store() && !op_kind.is_fence();

            if is_cas {
                // CAS: ordering_part is "success_failure" e.g. "acqrel_acquire"
                let (success, failure) = parse_cas_orderings(ordering_part)?;
                return Some(AtomicOperation {
                    place,
                    dest: if has_dest { Some(dest.clone()) } else { None },
                    op_kind,
                    ordering: success,
                    failure_ordering: Some(failure),
                    span: span.clone(),
                });
            } else {
                let ordering = parse_ordering(ordering_part)?;
                return Some(AtomicOperation {
                    place,
                    dest: if has_dest { Some(dest.clone()) } else { None },
                    op_kind,
                    ordering,
                    failure_ordering: None,
                    span: span.clone(),
                });
            }
        }
    }

    None
}

/// Parse Form B intrinsic: the operation name extracted from the function path.
/// Ordering comes from function arguments (const Ordering operand).
fn parse_form_b(
    op_name: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) -> AtomicIntrinsicMetadata {
    let (op_kind, is_cas) = match op_name {
        "load" => (AtomicOpKind::Load, false),
        "store" => (AtomicOpKind::Store, false),
        "exchange" | "swap" => (AtomicOpKind::Exchange, false),
        "compare_exchange" | "cxchg" => (AtomicOpKind::CompareExchange, true),
        "compare_exchange_weak" | "cxchgweak" => (AtomicOpKind::CompareExchangeWeak, true),
        "fetch_add" | "xadd" => (AtomicOpKind::FetchAdd, false),
        "fetch_sub" | "xsub" => (AtomicOpKind::FetchSub, false),
        "fetch_and" => (AtomicOpKind::FetchAnd, false),
        "fetch_or" => (AtomicOpKind::FetchOr, false),
        "fetch_xor" => (AtomicOpKind::FetchXor, false),
        "fetch_nand" => (AtomicOpKind::FetchNand, false),
        "fetch_min" => (AtomicOpKind::FetchMin, false),
        "fetch_max" => (AtomicOpKind::FetchMax, false),
        "fence" => (AtomicOpKind::Fence, false),
        "compiler_fence" | "singlethreadfence" => (AtomicOpKind::CompilerFence, false),
        _ => {
            return AtomicIntrinsicMetadata::Malformed {
                detail: format!("unrecognized generic atomic operation `{op_name}`"),
            };
        }
    };

    let place = extract_place_from_args(args, op_kind);
    let has_dest = !op_kind.is_store() && !op_kind.is_fence();

    // For Form B, ordering is in the arguments. Ordering arg positions vary:
    // load(ptr, ordering) -> ordering at index 1
    // store(ptr, val, ordering) -> ordering at index 2
    // CAS(ptr, old, new, success_ord, failure_ord) -> indices 3, 4
    // fetch_*(ptr, val, ordering) -> ordering at index 2
    // fence(ordering) -> ordering at index 0
    if is_cas {
        let Some(success) = ordering_from_args(args, 3) else {
            return AtomicIntrinsicMetadata::Malformed {
                detail: format!(
                    "{op_name} success ordering argument is missing or not a concrete Ordering discriminant"
                ),
            };
        };
        let Some(failure) = ordering_from_args(args, 4) else {
            return AtomicIntrinsicMetadata::Malformed {
                detail: format!(
                    "{op_name} failure ordering argument is missing or not a concrete Ordering discriminant"
                ),
            };
        };
        AtomicIntrinsicMetadata::Parsed(AtomicOperation {
            place,
            dest: if has_dest { Some(dest.clone()) } else { None },
            op_kind,
            ordering: success,
            failure_ordering: Some(failure),
            span: span.clone(),
        })
    } else {
        let ord_idx = match op_kind {
            AtomicOpKind::Fence | AtomicOpKind::CompilerFence => 0,
            AtomicOpKind::Load => 1,
            _ => 2, // store, exchange, fetch_*
        };
        let Some(ordering) = ordering_from_args(args, ord_idx) else {
            return AtomicIntrinsicMetadata::Malformed {
                detail: format!(
                    "{op_name} ordering argument is missing or not a concrete Ordering discriminant"
                ),
            };
        };
        AtomicIntrinsicMetadata::Parsed(AtomicOperation {
            place,
            dest: if has_dest { Some(dest.clone()) } else { None },
            op_kind,
            ordering,
            failure_ordering: None,
            span: span.clone(),
        })
    }
}

/// Parse an ordering string from an intrinsic name suffix.
fn parse_ordering(s: &str) -> Option<AtomicOrdering> {
    match s {
        "relaxed" => Some(AtomicOrdering::Relaxed),
        "acquire" | "consume" => Some(AtomicOrdering::Acquire), // Consume maps to Acquire
        "release" => Some(AtomicOrdering::Release),
        "acqrel" => Some(AtomicOrdering::AcqRel),
        "seqcst" => Some(AtomicOrdering::SeqCst),
        _ => None,
    }
}

/// Parse CAS dual ordering from suffix like "acqrel_acquire" or "seqcst_seqcst".
fn parse_cas_orderings(s: &str) -> Option<(AtomicOrdering, AtomicOrdering)> {
    // Try each known ordering as the success prefix (longest first to avoid ambiguity).
    let orderings = ["seqcst", "acqrel", "acquire", "release", "relaxed", "consume"];
    for &success_str in &orderings {
        if let Some(rest) = s.strip_prefix(success_str) {
            if let Some(failure_str) = rest.strip_prefix('_') {
                let success = parse_ordering(success_str)?;
                let failure = parse_ordering(failure_str)?;
                return Some((success, failure));
            }
        }
    }
    None
}

/// Extract the accessed place from call arguments.
///
/// For non-fence operations, the first argument is a raw pointer to the
/// atomic location. We extract the Place from the operand. For fence
/// operations, there is no memory location — use a synthetic Place::local(0).
fn extract_place_from_args(args: &[Operand], op_kind: AtomicOpKind) -> Place {
    if op_kind.is_fence() {
        return Place::local(0);
    }
    args.first()
        .and_then(|arg| match arg {
            Operand::Copy(p) | Operand::Move(p) => Some(p.clone()),
            _ => None,
        })
        .unwrap_or_else(|| Place::local(0))
}

/// Try to extract an ordering from a const argument at the given index.
///
/// In Form B intrinsics, ordering is passed as an explicit `Ordering` enum
/// argument. We look for uint constants that map to the discriminant values
/// of `std::sync::atomic::Ordering`.
fn ordering_from_args(args: &[Operand], index: usize) -> Option<AtomicOrdering> {
    let value = match args.get(index)? {
        Operand::Constant(ConstValue::Uint(value, _)) => *value,
        Operand::Constant(ConstValue::Int(value)) => u128::try_from(*value).ok()?,
        _ => return None,
    };

    // `std::sync::atomic::Ordering` discriminants in rustc MIR:
    // Relaxed=0, Release=1, Acquire=2, AcqRel=3, SeqCst=4.
    match value {
        0 => Some(AtomicOrdering::Relaxed),
        1 => Some(AtomicOrdering::Release),
        2 => Some(AtomicOrdering::Acquire),
        3 => Some(AtomicOrdering::AcqRel),
        4 => Some(AtomicOrdering::SeqCst),
        _ => None,
    }
}

// ---------------------------------------------------------------------------

/// Convert a rustc Rvalue.
fn convert_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &mir::Rvalue<'tcx>,
    local_decls: Option<&mir::LocalDecls<'tcx>>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Rvalue {
    match rvalue {
        mir::Rvalue::Use(mir::Operand::Constant(box const_op), _) => {
            convert_const_aggregate_rvalue(tcx, const_op)
                .unwrap_or_else(|| Rvalue::Use(convert_const_operand(tcx, const_op)))
        }
        mir::Rvalue::Use(op, _) => Rvalue::Use(convert_operand(tcx, op, typing_env)),

        mir::Rvalue::BinaryOp(bin_op, box (lhs, rhs)) => {
            let l = convert_operand(tcx, lhs, typing_env);
            let r = convert_operand(tcx, rhs, typing_env);
            // Trust: W2 inc-0 — `BinOp::Offset` is pointer arithmetic
            // (`ptr + count * size_of::<T>()`), the SAME operation as the
            // `core::ptr::{add,sub,offset}` intrinsic family, arriving as a MIR
            // BinOp. It is the sole blocker on the slice-iterator leaf family
            // (`Iter::next` cursor post-increment). Model it as the distinguishable
            // `Rvalue::PtrOffset { ptr, count }` — carrying the base pointer and the
            // element offset — instead of erasing it to an opaque `Unsupported`
            // marker, so downstream can converge it onto the intrinsic lane's
            // `(base slice, index)` `PtrModel` and its fail-closed in-bounds VC.
            // Fail-closed until then: vcgen emits an `UnsupportedMir`-class
            // in-bounds obligation for `PtrOffset`, so no function with an
            // un-discharged offset can certify.
            if matches!(bin_op, mir::BinOp::Offset) {
                return Rvalue::PtrOffset { ptr: l, count: r };
            }
            let Some((our_op, checked)) = convert_supported_binop(*bin_op) else {
                return unsupported_rvalue(
                    format!("BinOp::{bin_op:?}"),
                    "operation requires explicit MIR semantics before proof".to_string(),
                    vec![l, r],
                );
            };

            if checked {
                Rvalue::CheckedBinaryOp(our_op, l, r)
            } else {
                Rvalue::BinaryOp(our_op, l, r)
            }
        }

        mir::Rvalue::UnaryOp(un_op, operand) => {
            let op = match un_op {
                mir::UnOp::Not => UnOp::Not,
                mir::UnOp::Neg => UnOp::Neg,
                // Trust: #386 — map PtrMetadata to its own variant instead
                // of incorrectly falling back to Not.
                mir::UnOp::PtrMetadata => UnOp::PtrMetadata,
            };
            Rvalue::UnaryOp(op, convert_operand(tcx, operand, typing_env))
        }

        mir::Rvalue::Ref(_, borrow_kind, place) => {
            let place = convert_place(tcx, place, typing_env);
            convert_ref_rvalue(*borrow_kind, place)
        }

        mir::Rvalue::ThreadLocalRef(def_id) => unsupported_rvalue(
            "Rvalue::ThreadLocalRef",
            format!("thread-local reference to {}", crate::safe_def_path_str(tcx, *def_id)),
            vec![],
        ),

        mir::Rvalue::Cast(kind, operand, ty) => {
            // Capture the operand's SOURCE type before `convert_operand` shadows it
            // (needed to soundly gate the pointer->integer `Transmute` leg below).
            // `None` when no local_decls are available (synthetic-fixture rvalues),
            // in which case the ptr->int leg stays fail-closed.
            let src_ty = local_decls.map(|ld| operand.ty(ld, tcx));
            let operand = convert_operand(tcx, operand, typing_env);
            match kind {
                mir::CastKind::IntToInt
                | mir::CastKind::FloatToInt
                | mir::CastKind::FloatToFloat
                | mir::CastKind::IntToFloat
                | mir::CastKind::PtrToPtr => {
                    Rvalue::Cast(operand, convert_ty_with_env(tcx, typing_env, *ty))
                }
                mir::CastKind::PointerCoercion(
                    PointerCoercion::ReifyFnPointer(_)
                    | PointerCoercion::ClosureFnPointer(_)
                    | PointerCoercion::UnsafeFnPointer
                    | PointerCoercion::MutToConstPointer
                    | PointerCoercion::ArrayToPointer,
                    _,
                ) => Rvalue::Cast(operand, convert_ty_with_env(tcx, typing_env, *ty)),
                mir::CastKind::Transmute => {
                    // A transmute whose TARGET is a thin pointer / box (the `vec!`/
                    // `Box` machinery's `*mut u8 -> Box<MaybeUninit<T>>` and
                    // `NonNull<_> -> *const MaybeUninit<T>`) preserves the address
                    // bits — only the pointee TYPE label changes — so model it as a
                    // value-preserving `Cast`. trust-mc threads the pointer through
                    // its single-pointer-newtype wrap/unwrap; the deref's own
                    // validity obligation handles pointee validity SEPARATELY. All
                    // OTHER transmutes (value/layout reinterpretation, e.g.
                    // `f64 -> u64`) stay Unsupported — fail-closed. A pointer->integer
                    // transmute (the `*const _ -> usize` alignment-check leg) is ALSO
                    // value-preserving on the address bits; allow it ONLY when the
                    // SOURCE is a pointer (so a value transmute to an integer stays
                    // fail-closed). The bridge cast-op selector lowers a
                    // pointer-source->integer cast to `PtrToInt`.
                    let ptr_to_int =
                        src_ty.as_ref().is_some_and(|t| t.is_any_ptr()) && ty.is_integral();
                    // Trust (async plumbing, piece #13): the async-resume shim rustc
                    // itself generates transmutes `&mut Context<'_> -> NonNull<Context>`.
                    // `NonNull<T>` is `#[repr(transparent)]` over `*const T` (a std
                    // layout GUARANTEE), so a pointer/reference-source transmute into it
                    // is address-preserving — the same class as the thin-pointer legs
                    // above; only the type label changes, and the deref's own validity
                    // obligation covers pointee validity separately. Gated on BOTH the
                    // pointer source AND the std `NonNull` target (a value transmute
                    // into NonNull, e.g. `usize -> NonNull<T>`, stays fail-closed).
                    let ptr_to_nonnull = src_ty.as_ref().is_some_and(|t| t.is_any_ptr())
                        && ty.ty_adt_def().is_some_and(|def| {
                            tcx.is_diagnostic_item(rustc_span::sym::NonNull, def.did())
                        });
                    if ty.is_any_ptr() || ty.is_box() || ptr_to_int || ptr_to_nonnull {
                        Rvalue::Cast(operand, convert_ty_with_env(tcx, typing_env, *ty))
                    } else {
                        unsupported_rvalue(
                            "CastKind::Transmute",
                            format!(
                                "transmute to {ty:?} requires layout compatibility and validity-invariant proof; refusing to model it as a value-preserving cast"
                            ),
                            vec![operand],
                        )
                    }
                }
                mir::CastKind::FnPtrToPtr => unsupported_rvalue(
                    "CastKind::FnPtrToPtr",
                    format!(
                        "function pointer cast to {ty:?} requires callable address/provenance semantics"
                    ),
                    vec![operand],
                ),
                // `ptr as usize` (expose) / `usize as *T` (recover): the cast itself is TOTAL —
                // no panic, no overflow, no alloc. The exposed ADDRESS value and the recovered
                // PROVENANCE are the unsafe caller's SAFETY contract, not a verifier panic/UB
                // obligation, so lower the RESULT to the sound `OpaqueConst` over-approximation
                // (unconstrained, never falsely proved): `(ptr as usize) % a == 0` gets an opaque
                // bool, and a later deref of a recovered opaque pointer fails closed. Unblocks the
                // common `(ptr as usize).is_multiple_of(align)` alignment-check idiom.
                mir::CastKind::PointerExposeProvenance
                | mir::CastKind::PointerWithExposedProvenance => {
                    Rvalue::Use(Operand::Constant(ConstValue::OpaqueConst))
                }
                // `&[T; N] -> &[T]` (array→slice unsize): the bridge's
                // array_to_slice_pointer_cast lowers this precisely — the slice
                // carries the array's statically-known length N. Model it as a
                // value cast to the slice-ref target instead of refusing. Other
                // unsize coercions (trait objects → vtables) stay unsupported.
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _)
                    if unsize_target_is_slice_ref(*ty) =>
                {
                    Rvalue::Cast(operand, convert_ty_with_env(tcx, typing_env, *ty))
                }
                // `&T -> &dyn Trait` (trait-object unsize): an infallible vtable
                // attach (no panic/overflow/alloc). The vtable + pointee contents are
                // not modeled, so lower the RESULT to the same sound `OpaqueConst`
                // over-approximation used for unmodelable constants — never falsely
                // Proved (unconstrained value), but the function proceeds instead of
                // wedging the whole obligation at `unsupported_mir`. This is what
                // unblocks the derived `Debug::fmt`/`Hash`/… boilerplate that dominates
                // the gap. (Slice unsize above stays a precise cast — it carries the
                // length; only trait objects, whose metadata we don't use, go opaque.)
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _)
                    if unsize_target_is_trait_object_ref(*ty) =>
                {
                    Rvalue::Use(Operand::Constant(ConstValue::OpaqueConst))
                }
                mir::CastKind::PointerCoercion(coercion, source) => unsupported_rvalue(
                    format!("CastKind::PointerCoercion::{coercion:?}"),
                    format!(
                        "pointer coercion from {source:?} to {ty:?} requires metadata/provenance semantics"
                    ),
                    vec![operand],
                ),
                mir::CastKind::Subtype => unsupported_rvalue(
                    "CastKind::Subtype",
                    format!("subtype cast to {ty:?} requires type-metadata semantics before proof"),
                    vec![operand],
                ),
            }
        }

        mir::Rvalue::Aggregate(box mir::AggregateKind::Tuple, operands) if operands.is_empty() => {
            // Native MIR spells `()` as an empty tuple aggregate in some paths.
            // Canonicalize it to a unit constant so downstream lowering does not
            // materialize an uninitialized zero-field aggregate.
            Rvalue::Use(Operand::Constant(ConstValue::Unit))
        }

        mir::Rvalue::Aggregate(box agg_kind, operands) => {
            let kind = match agg_kind {
                mir::AggregateKind::Tuple => AggregateKind::Tuple,
                mir::AggregateKind::Array(_) => AggregateKind::Array,
                mir::AggregateKind::Adt(def_id, variant_idx, adt_args, _, active_field) => {
                    AggregateKind::Adt {
                        name: crate::safe_def_path_str(tcx, *def_id),
                        variant: variant_idx.as_usize(),
                        active_field: active_field.map(|field| field.as_usize()),
                        // Trust (C1): these args were discarded. Both sides of the derived-vs-built
                        // comparison run through this converter, so carrying them makes a
                        // wrong-args reconstruction visible to the comparator for the first time.
                        args: Some(crate::safe_def_path_str_with_args(tcx, *def_id, adt_args)),
                    }
                }
                mir::AggregateKind::Closure(def_id, args) => {
                    // Trust: #20 — closure aggregates lower into trust-ir with
                    // captured-environment shape and call kind, so downstream
                    // VC-gen can model the closure as a
                    //   (captures: struct, body: fn(captures, args) -> ret)
                    // pair with symbolic captures.
                    //
                    // Trust: M6 rung 7 — captures MUST be lowered with the SAME
                    // `typing_env` as the enclosing body's locals (`extract_body`'s
                    // `ty_convert::convert_ty_in_env(tcx, typing_env, decl.ty)`), not
                    // the plain, alias-normalization-disabled `convert_ty`. A capture's
                    // upvar type and the captured operand's declared local type are the
                    // SAME nominal rustc `Ty` (the closure captures the place directly),
                    // so `closure_aggregate_support_error`'s capture/operand type-equality
                    // check (trust-vcgen) requires both sides to lower identically. Before
                    // this fix they diverged whenever the shared type recursed through an
                    // alias/opaque position deep enough to need normalization: the local's
                    // `convert_ty_in_env` call could reveal it down to a modeled
                    // `Ty::Datatype` back-reference, while this call site's env-less
                    // `convert_ty` bailed to `Ty::Unsupported` at that same node —
                    // spuriously failing the equality check and stamping a real,
                    // capture-light closure aggregate `UnsupportedMir` (13 judge-corpus
                    // instances: `expr::subst`'s `fold_expr_opt`/`fold_const_opt` family +
                    // `beta_normalize`/`collect_constants_into`/`has_loose_bvar_in_range`,
                    // all captures of `&Expr`/`&mut Abstractor`-shaped recursive ADTs).
                    // Falls back to the plain (env-less) conversion when no typing_env is
                    // available (synthetic/test call sites), matching the local_decls:
                    // `None` fallback convention already used elsewhere in this function.
                    let closure_args = args.as_closure();
                    let captures: Vec<Ty> = closure_args
                        .upvar_tys()
                        .iter()
                        .map(|upvar_ty| convert_ty_with_env(tcx, typing_env, upvar_ty))
                        .collect();
                    // `kind_ty().to_opt_closure_kind()` is the inference-safe
                    // variant — `as_closure().kind()` panics if the closure
                    // kind type variable is still an inference variable. By
                    // the time we run on optimized/analysis MIR the kind is
                    // resolved, but defaulting to `FnOnce` (the weakest /
                    // most general) keeps us safe if anything ever calls this
                    // pre-inference.
                    let call_kind = match closure_args.kind_ty().to_opt_closure_kind() {
                        Some(ty::ClosureKind::Fn) => ClosureCallKind::Fn,
                        Some(ty::ClosureKind::FnMut) => ClosureCallKind::FnMut,
                        Some(ty::ClosureKind::FnOnce) | None => ClosureCallKind::FnOnce,
                    };
                    AggregateKind::Closure {
                        name: crate::safe_def_path_str(tcx, *def_id),
                        captures,
                        call_kind,
                    }
                }
                mir::AggregateKind::Coroutine(def_id, _) => {
                    AggregateKind::Coroutine { name: crate::safe_def_path_str(tcx, *def_id) }
                }
                mir::AggregateKind::CoroutineClosure(def_id, _) => {
                    AggregateKind::CoroutineClosure { name: crate::safe_def_path_str(tcx, *def_id) }
                }
                // Trust: M6 rung-7 sweep — the fat/thin pointee type embedded in a raw
                // pointer aggregate is a body-embedded `Ty`, architecturally the same
                // shape as a `Cast` target: thread `typing_env` through it too, so a
                // `pointee_ty` that recurses through an alias/opaque position gets the
                // same normalization chance as everything else instead of spuriously
                // failing `raw_ptr_aggregate_support_error`'s
                // `single_lane_raw_ptr_pointee_error` unsupported-pointee gate
                // (trust-vcgen) on a type that would otherwise resolve.
                mir::AggregateKind::RawPtr(pointee_ty, mutability) => AggregateKind::RawPtr {
                    pointee_ty: convert_ty_with_env(tcx, typing_env, *pointee_ty),
                    mutable: mutability.is_mut(),
                },
            };
            let ops: Vec<Operand> =
                operands.iter().map(|op| convert_operand(tcx, op, typing_env)).collect();
            Rvalue::Aggregate(kind, ops)
        }

        mir::Rvalue::Discriminant(place) => {
            Rvalue::Discriminant(convert_place(tcx, place, typing_env))
        }

        mir::Rvalue::Repeat(operand, count) => {
            // Unknown repeat counts must not become zero-length arrays: that
            // would under-approximate valid MIR and can produce false proofs.
            match count.try_to_target_usize(tcx).and_then(|v| usize::try_from(v).ok()) {
                Some(n) => Rvalue::Repeat(convert_operand(tcx, operand, typing_env), n),
                // A const-generic repeat `[x; N]` (N unresolved, e.g. `ArrayVec<T, const N>`'s
                // `[uninit; N]` backing) -> a sound opaque array: its length is unknown, so any
                // index into it fails closed (the bounds obligation cannot be discharged) and the
                // result value is unconstrained — never falsely proved.
                None => Rvalue::Use(Operand::Constant(ConstValue::OpaqueConst)),
            }
        }

        mir::Rvalue::RawPtr(ptr_kind, place) => {
            let converted_place = convert_place(tcx, place, typing_env);
            match ptr_kind {
                mir::RawPtrKind::Mut => Rvalue::AddressOf(true, converted_place),
                mir::RawPtrKind::Const => Rvalue::AddressOf(false, converted_place),
                // Trust: a `FakeForPtrMetadata` raw pointer is the compiler's
                // device for reading a place's pointer METADATA (a slice's length
                // via `<[T]>::len()`, notably on a `&mut [T]` where the index/guard
                // path re-reads it): `_p = &raw const *slice_ref; _len =
                // PtrMetadata(_p)`. The pointer VALUE is never used — only its
                // metadata — so model it as an ordinary const raw pointer to the
                // place; `slice_len_formula` (raw-ptr-to-slice) + the `AddressOf`
                // block def then tie `_p`'s `__slice_len` to the referent slice's
                // length. Previously Unsupported, which false-refuted the ubiquitous
                // guarded `&mut [T]` index `if i < dst.len() { dst[i] = .. }`.
                mir::RawPtrKind::FakeForPtrMetadata => Rvalue::AddressOf(false, converted_place),
            }
        }

        mir::Rvalue::CopyForDeref(place) => {
            Rvalue::CopyForDeref(convert_place(tcx, place, typing_env))
        }

        mir::Rvalue::WrapUnsafeBinder(operand, ty) => unsupported_rvalue(
            "Rvalue::WrapUnsafeBinder",
            format!("unsafe binder wrapping value of type {ty:?} needs binder-aware semantics"),
            vec![convert_operand(tcx, operand, typing_env)],
        ),

        // Trust: rust 1.99 added `Rvalue::Reborrow(Ty, Mutability, Place)` — a bitwise
        // copy of a place that reborrows it through the user-implementable `Reborrow` /
        // `CoerceShared` traits (a custom-ADT analogue of `&mut T`/`&T` reborrowing).
        // The result is an ADT value whose reborrow-trait aliasing semantics are not
        // modeled here (and are still in flux upstream), so we fail closed rather than
        // assert it behaves as a plain `&place`. Sound: any use of the handle stays
        // conservative; it never yields a false proof. The op itself is infallible.
        mir::Rvalue::Reborrow(_, mutability, place) => unsupported_rvalue(
            "Rvalue::Reborrow",
            format!(
                "{mutability:?} reborrow of a user ADT via the Reborrow/CoerceShared trait needs reborrow-aliasing semantics"
            ),
            vec![Operand::Copy(convert_place(tcx, place, typing_env))],
        ),
    }
}

fn unsupported_rvalue(kind: impl Into<String>, detail: String, operands: Vec<Operand>) -> Rvalue {
    Rvalue::Unsupported { kind: kind.into(), detail, operands }
}

/// True when an unsize-cast target is a reference to a slice/str (`&[T]`/`&str`),
/// i.e. the `&[T; N] -> &[T]` array→slice coercion the bridge can lower precisely.
/// Trait-object unsize targets (`&dyn Trait`) return false and stay unsupported.
fn unsize_target_is_slice_ref(ty: rustc_middle::ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::Ref(_, inner, _) => {
            matches!(inner.kind(), ty::TyKind::Slice(_) | ty::TyKind::Str)
        }
        _ => false,
    }
}

/// True when an unsize-cast target is a reference (or raw pointer) to a trait
/// object (`&dyn Trait` / `*const dyn Trait`), i.e. the `&T -> &dyn Trait`
/// coercion produced pervasively by `Debug`/`Display`/`format!` boilerplate.
/// The coercion only attaches a vtable pointer — infallible, no panic/overflow/alloc —
/// and we model neither the vtable nor the pointee, so the result is lowered to the
/// sound `OpaqueConst` over-approximation. Unconstrained: obligations that depend on
/// the value stay Unknown/Failed (never falsely Proved); obligations that don't (the
/// derived `Debug::fmt` boilerplate dominating the gap) become reachable.
fn unsize_target_is_trait_object_ref(ty: rustc_middle::ty::Ty<'_>) -> bool {
    let inner = match ty.kind() {
        ty::TyKind::Ref(_, inner, _) => *inner,
        ty::TyKind::RawPtr(inner, _) => *inner,
        _ => return false,
    };
    matches!(inner.kind(), ty::TyKind::Dynamic(..))
}

fn convert_ref_rvalue(borrow_kind: mir::BorrowKind, place: Place) -> Rvalue {
    match borrow_kind {
        mir::BorrowKind::Shared => Rvalue::Ref { mutable: false, place },
        // verifier-coverage: all mutable-borrow kinds lower to a `&mut T`.
        // Default, TwoPhaseBorrow (reserve-then-activate), and ClosureCapture are
        // borrow-checker timing/capture distinctions on a borrow that, in the
        // post-borrowck MIR we extract, is an ordinary `&mut`. No value-level
        // safety obligation (overflow/bounds/div-zero) depends on the
        // distinction — the referent and the reference type are identical to
        // Default — so lowering them uniformly is sound: it neither strengthens
        // nor weakens any obligation. Fake borrows stay unsupported below; they
        // are pure borrow-check artifacts with no runtime reference.
        mir::BorrowKind::Mut { .. } => Rvalue::Ref { mutable: true, place },
        mir::BorrowKind::Fake(kind) => unsupported_rvalue(
            format!("BorrowKind::Fake::{kind:?}"),
            format!("fake borrow kind {kind:?} requires shallow/deep borrow semantics"),
            vec![Operand::Copy(place)],
        ),
    }
}

fn convert_supported_binop(op: mir::BinOp) -> Option<(BinOp, bool)> {
    match op {
        mir::BinOp::Add => Some((BinOp::Add, false)),
        mir::BinOp::AddUnchecked => Some((BinOp::Add, false)),
        mir::BinOp::AddWithOverflow => Some((BinOp::Add, true)),
        mir::BinOp::Sub => Some((BinOp::Sub, false)),
        mir::BinOp::SubUnchecked => Some((BinOp::Sub, false)),
        mir::BinOp::SubWithOverflow => Some((BinOp::Sub, true)),
        mir::BinOp::Mul => Some((BinOp::Mul, false)),
        mir::BinOp::MulUnchecked => Some((BinOp::Mul, false)),
        mir::BinOp::MulWithOverflow => Some((BinOp::Mul, true)),
        mir::BinOp::Div => Some((BinOp::Div, false)),
        mir::BinOp::Rem => Some((BinOp::Rem, false)),
        mir::BinOp::BitXor => Some((BinOp::BitXor, false)),
        mir::BinOp::BitAnd => Some((BinOp::BitAnd, false)),
        mir::BinOp::BitOr => Some((BinOp::BitOr, false)),
        mir::BinOp::Shl => Some((BinOp::Shl, false)),
        mir::BinOp::ShlUnchecked => None,
        mir::BinOp::Shr => Some((BinOp::Shr, false)),
        mir::BinOp::ShrUnchecked => None,
        mir::BinOp::Eq => Some((BinOp::Eq, false)),
        mir::BinOp::Lt => Some((BinOp::Lt, false)),
        mir::BinOp::Le => Some((BinOp::Le, false)),
        mir::BinOp::Ne => Some((BinOp::Ne, false)),
        mir::BinOp::Ge => Some((BinOp::Ge, false)),
        mir::BinOp::Gt => Some((BinOp::Gt, false)),
        // Three-way comparison returns -1/0/1, not a boolean.
        mir::BinOp::Cmp => Some((BinOp::Cmp, false)),
        mir::BinOp::Offset => None,
    }
}

/// Convert a rustc Operand.
///
/// Trust: Exhaustive match — no wildcard fallback. If rustc adds new Operand
/// variants, this will fail to compile, which is the correct behavior.
fn convert_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &mir::Operand<'tcx>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Operand {
    match operand {
        mir::Operand::Copy(place) => Operand::Copy(convert_place(tcx, place, typing_env)),
        mir::Operand::Move(place) => Operand::Move(convert_place(tcx, place, typing_env)),
        mir::Operand::Constant(box const_op) => convert_const_operand(tcx, const_op),
        mir::Operand::RuntimeChecks(check) => {
            Operand::Constant(ConstValue::Bool(check.value(tcx.sess)))
        }
    }
}

/// Convert a rustc ConstOperand to our Operand.
/// Trust: piece #7a — if this MIR constant is a const-generic PARAM (`N`),
/// return its `(index, name)` identity. A const-generic value operand appears in
/// MIR as `mir::Const::Ty(_, ty_const)` whose `.kind()` is
/// `ConstKind::Param(ParamConst)` (see `promote_consts.rs`: "`Const::Ty` is always
/// a `ConstKind::Param` right now"). We also peel a `Const::Unevaluated` whose
/// resolved kind is a bare `Param`, so a `const N` used directly still recovers
/// its identity. Returns `None` for every non-param const (assoc-const,
/// `size_of`, literal), which stays on the existing `OpaqueScalar`/value path.
fn const_param_identity<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<(u32, String)> {
    use rustc_middle::ty::ConstKind;
    let ty_const = match const_op.const_ {
        mir::Const::Ty(_, ty_const) => ty_const,
        // A `Const::Unevaluated`/`Const::Val` is not a bare param identity here.
        _ => return None,
    };
    match ty_const.kind() {
        ConstKind::Param(p) => Some((p.index, p.name.to_string())),
        _ => {
            // A const-param can also appear behind a normalizable wrapper; try one
            // normalization pass and re-inspect. Fail-closed to None otherwise.
            let normalized = tcx
                .try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    ty::Unnormalized::new_wip(ty_const),
                )
                .unwrap_or(ty_const);
            match normalized.kind() {
                ConstKind::Param(p) => Some((p.index, p.name.to_string())),
                _ => None,
            }
        }
    }
}

// Trust: eval a MIR const to bits ONLY when it is actually monomorphic.
// A generic body can carry `<<F as Trait>::Assoc as Trait2>::CONST` whose
// projection args don't normalize under reveal-all; forcing eval routes into
// resolve_instance -> normalize_erasing_regions -> NoSolution bug! (ICE).
// Mirrors const_operand_value's guard (`has_non_region_param()`, below).
// Fail-soft to None so the caller degrades to OpaqueScalar (sound: a generic
// const has no single value). `try_eval_bits` derives its size internally.
fn try_eval_bits_mono<'tcx>(c: mir::Const<'tcx>, tcx: TyCtxt<'tcx>) -> Option<u128> {
    if c.has_non_region_param() {
        return None;
    }
    c.try_eval_bits(tcx, ty::TypingEnv::fully_monomorphized())
}

fn callable_def_path_hash(
    tcx: TyCtxt<'_>,
    def_id: rustc_span::def_id::DefId,
) -> CallableDefPathHash {
    // rustc's DefPathHash is stable across sessions and contains a
    // StableCrateId plus a crate-local hash. rustc actively checks both
    // collision domains and aborts compilation on a collision; preserve the
    // checked components losslessly instead of relying on the diagnostic
    // def-path string, which is ambiguous across same-named crate instances.
    let hash = tcx.def_path_hash(def_id);
    CallableDefPathHash::new(hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}

fn convert_const_operand<'tcx>(tcx: TyCtxt<'tcx>, const_op: &mir::ConstOperand<'tcx>) -> Operand {
    use rustc_middle::ty::TyKind;

    let c = const_op.const_;
    let ty = c.ty();

    // Type-directed constant extraction (check type FIRST to avoid panics)
    match ty.kind() {
        TyKind::Bool => {
            if let Some(b) = c.try_to_bool() {
                return Operand::Constant(ConstValue::Bool(b));
            }
        }
        TyKind::Char => {
            let size = rustc_abi::Size::from_bits(32);
            // `try_to_bits` only reads an ALREADY-evaluated `Const::Val`; a
            // `Const::Unevaluated` (e.g. a named `const C: char = …` reference,
            // which MIR keeps as `const path::C`) needs `try_eval_bits`, which
            // resolves+evaluates it. Falling back recovers the concrete value
            // instead of degrading to an unconstrained `OpaqueScalar` below.
            if let Some(bits) = c.try_to_bits(size).or_else(|| try_eval_bits_mono(c, tcx)) {
                return Operand::Constant(ConstValue::Uint(bits, 32));
            }
        }
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            // See the `Char` arm: evaluate a `Const::Unevaluated` named const
            // (`const N: i32 = …`) rather than opaquing it, so value-dependent
            // obligations (shift-amount `< width`, div-by-const, bounds) prove.
            if let Some(bits) = c.try_to_bits(size).or_else(|| try_eval_bits_mono(c, tcx)) {
                // Sign-extend the bits to i128
                let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
                return Operand::Constant(ConstValue::Int(val));
            }
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            // See the `Char` arm: evaluate a `Const::Unevaluated` named const
            // (`const R: u32 = 47`, the MurmurHash shift amount) rather than
            // opaquing it — this is what lets `k >> R`'s Shr-overflow VC prove
            // `R < 64` instead of leaving R an unconstrained `OpaqueScalar`.
            if let Some(bits) = c.try_to_bits(size).or_else(|| try_eval_bits_mono(c, tcx)) {
                return Operand::Constant(ConstValue::Uint(bits, width));
            }
        }
        // Trust: Extract float constants from MIR. Float bits are
        // IEEE 754; convert via f32/f64 from_bits to get the actual value.
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let size = rustc_abi::Size::from_bits(width as u64);
            if let Some(bits) = c.try_to_bits(size) {
                return match width {
                    32 | 64 => Operand::Constant(ConstValue::FloatBits { bits, width }),
                    16 | 128 => unsupported_operand(
                        format!("Const::{float_ty:?}"),
                        format!("float constant width {width} needs dedicated float encoding"),
                    ),
                    _ => unreachable!("rustc FloatTy widths are enumerated above"),
                };
            }
        }
        // a `&str` literal — carry its UTF-8 bytes. We check the type
        // is `&str` FIRST because `try_get_slice_bytes_for_diagnostics` bug!s on
        // non-slice constants. That method is rustc's own string-printing path
        // and is reliable for genuine string literals (their allocations are
        // fully initialized). Any extraction miss (e.g. an indirect/dangling
        // reference we can't read) falls through to the fail-closed
        // `unsupported_operand` below — never to a guessed value.
        TyKind::Ref(_, inner, _) if matches!(inner.kind(), TyKind::Str) => {
            if let mir::Const::Val(val, _) = c {
                if let Some(bytes) = val.try_get_slice_bytes_for_diagnostics(tcx) {
                    return Operand::Constant(ConstValue::Str { bytes: bytes.to_vec() });
                }
            }
        }
        // Trust Gap 3 (build #25): a reference-to-slice/array constant — a static
        // lookup table (`&[&str]`, `&[Enum]`, `&[T; N]`), the dominant
        // "unsupported constant" blocker. Its concrete contents aren't modeled;
        // lower to an opaque fresh-symbolic slice fat pointer (like a `&str`
        // literal). Sound over-approximation: length/contents are unconstrained,
        // so value-dependent obligations stay `unknown`, never falsely proved.
        TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), TyKind::Slice(_) | TyKind::Array(_, _)) =>
        {
            // T7 (fmt-template bytes): a reference-to-BYTE-ARRAY constant whose
            // contents are fully readable carries its exact bytes as
            // `ConstValue::Str` — the dominant instance is the `format_args!`
            // TEMPLATE (`&[u8; N]`, e.g. `b"\x07prefix \xc0\x00"`) handed to
            // `core::fmt::Arguments::new::<N, M>` by every formatted
            // `panic!`/`assert!` on this toolchain. Without the bytes, the
            // trust-vcgen contract-panic matcher can never see the
            // format-string literal pieces, forcing const-message rewrites in
            // user code (the aterm-alloc evidence). SOUND: `ConstValue::Str`
            // lowers to the same injectively-named OPAQUE symbol / fat-pointer
            // treatment as `OpaqueConst` (see trust-ir-bridge lower + the Str
            // doc in trust-types) — contents are never content-asserted, and
            // the injective name is keyed on the exact byte sequence, so two
            // DISTINCT byte arrays can never alias one symbol. The valtree read
            // (`str_ref_bytes_from_value` peels the ref and reads raw bytes) is
            // exact-or-None; any miss degrades to the pre-existing
            // fresh-symbolic `OpaqueConst` below, never to a guessed value.
            // (edition 2021 — no let-chains: nested ifs.)
            if let TyKind::Array(elem, len) = inner.kind() {
                if *elem != tcx.types.u8 {
                    return Operand::Constant(ConstValue::OpaqueConst);
                }
                // Optimized MIR commonly materializes a promoted byte string as
                // `Const::Val` scalar pointer rather than a type-level valtree.
                // Read exactly the statically-sized initialized allocation
                // range and reject provenance/uninit instead of using rustc's
                // slice diagnostic helper (which deliberately bug!s for sized
                // array references).
                if let Some(byte_len) = len.try_to_target_usize(tcx) {
                    if let mir::Const::Val(value, _) = c {
                        if let Some(bytes) =
                            byte_array_ref_bytes_from_const_value(tcx, value, byte_len)
                        {
                            return Operand::Constant(ConstValue::Str { bytes });
                        }
                    }
                }
                if let Some(value) = const_operand_value(tcx, const_op) {
                    if let Some(bytes) = str_ref_bytes_from_value(tcx, value) {
                        return Operand::Constant(ConstValue::Str { bytes });
                    }
                }
                // Directly-evaluated (`Const::Val`) byte template — the dominant
                // `Arguments::new` format-template form, which `const_operand_value` returns
                // `None` for; read the array bytes from its allocation.
                if let Some(bytes) = array_ref_u8_const_bytes(tcx, &const_op.const_) {
                    return Operand::Constant(ConstValue::Str { bytes });
                }
            }
            // THIS toolchain's `Arguments::new(pieces, args)` format template is a `&[&str; N]`
            // PIECES array (not the `&[u8; N]` byte template above). Extract + concatenate its
            // literal pieces as an opaque `Str` so the contract-panic matcher can see a formatted
            // panic's message; any non-`&str` `&[T]` table (or a read miss) stays `OpaqueConst`.
            if let Some(value) = const_operand_value(tcx, const_op) {
                if let Some(bytes) = str_pieces_ref_bytes_from_value(tcx, value) {
                    return Operand::Constant(ConstValue::Str { bytes });
                }
            }
            return Operand::Constant(ConstValue::OpaqueConst);
        }
        // A non-capturing closure appears as a `Const` of `TyKind::Closure` —
        // e.g. the `|x| ...` handed to `Iterator::map`. Capturing closures are
        // MIR aggregates (see `AggregateKind::Closure`), so only an upvar-free
        // closure is admissible here. Preserve its exact safe def-path for
        // syntactic recognizers while downstream value models continue to
        // treat `CallableItem` as unit/opaque sorted. This identity is evidence,
        // never a solver fact.
        TyKind::Closure(def_id, args) => {
            if !args.as_closure().upvar_tys().is_empty() {
                return unsupported_operand(
                    "Const::Closure",
                    format!(
                        "capturing closure constant {} must be represented as an aggregate",
                        crate::safe_def_path_str(tcx, *def_id)
                    ),
                );
            }
            return Operand::Constant(ConstValue::CallableItem {
                def_path: crate::safe_def_path_str(tcx, *def_id),
                kind: CallableKind::Closure,
                def_path_hash: callable_def_path_hash(tcx, *def_id),
            });
        }
        // Function item values are zero-sized singletons, but their identity is
        // load-bearing when passed as callbacks. Preserve the exact safe
        // def-path without pretending to model function-pointer provenance.
        TyKind::FnDef(def_id, _) => {
            return Operand::Constant(ConstValue::CallableItem {
                def_path: crate::safe_def_path_str(tcx, *def_id),
                kind: CallableKind::FnDef,
                def_path_hash: callable_def_path_hash(tcx, *def_id),
            });
        }
        // Fieldless structs such as `std::alloc::Global` are zero-sized
        // singletons. As call operands they carry no runtime data, and there is
        // no variant identity to preserve. Multi-variant fieldless enums are
        // deliberately excluded below because their discriminant is a real value.
        TyKind::Adt(..) if is_fieldless_singleton_struct_ty(ty) => {
            return Operand::Constant(ConstValue::Unit);
        }
        _ => {}
    }

    if let Some(value) = const_operand_value(tcx, const_op) {
        // Trust: nested string-ref consts — the `&&str` that `x == "lit"`
        // produces by auto-ref'ing the literal — carry the same bytes as a
        // plain `&str`. Peel the reference layers and reuse the injectively
        // named `ConstValue::Str` rather than failing closed, which clears the
        // spurious Unsupported obligation on the ubiquitous comparison path.
        if let Some(bytes) = str_ref_bytes_from_value(tcx, value) {
            return Operand::Constant(ConstValue::Str { bytes });
        }
        // Trust (eq-guard channel): a promoted `&Option<T>::None`-style const —
        // the `_4 = const f::promoted[0]` that `o == None` produces — recovers
        // its variant identity instead of degrading to the fresh-symbolic
        // `OpaqueConst` below, which hides the None-ness from the equality
        // guard models. A payload-carrying pointee (`&Some(5)`) falls through.
        if let Some(cv) = std_enum_unit_variant_ref_const(tcx, value) {
            return Operand::Constant(cv);
        }
        let ty_const = ty::Const::new_value(tcx, value.valtree, value.ty);
        if let Some(operand) = convert_ty_const_to_operand(tcx, ty_const) {
            return operand;
        }
    }

    // Unit type
    if ty.is_unit() {
        return Operand::Constant(ConstValue::Unit);
    }

    // Trust verifier-coverage: an aggregate/opaque constant we can't lower to a
    // precise scalar — an empty `Vec`/`VecDeque` (whose `RawVec::NEW` backing is
    // an ADT aggregate, cap 0), a `Cell::new(c)`, a thread-local `LocalKey`, an
    // alloc handle, etc. Rather than fail closed to an `UnsupportedMir` VC (which
    // forces the WHOLE obligation to Unknown and strands every downstream check
    // in the function), degrade to the existing sound, fresh-symbolic
    // `OpaqueConst` sentinel — the same over-approximation already used for the
    // `&[&str]`/slice constant tables above (build #25). Its value is
    // unconstrained, so any obligation that genuinely depends on it stays
    // satisfiable-as-negation (Unknown/Failed), never falsely Proved; obligations
    // that do NOT depend on it (the common case for collection constructors) are
    // now reachable and discharge normally instead of being wedged at Unknown.
    if const_operand_value(tcx, const_op).is_some()
        || matches!(const_op.const_, mir::Const::Val(..))
    {
        return Operand::Constant(ConstValue::OpaqueConst);
    }

    // Any REFERENCE constant we could not lower precisely above — a promoted /
    // `Unevaluated` `&char`, non-literal `&str`, `&Option<char>`, `&RangeInclusive`,
    // or other `&T` const read in a generic body where const-eval is unavailable —
    // degrades to a fresh-symbolic opaque value instead of poisoning the whole
    // function into Unsupported. Sound: `OpaqueConst` asserts nothing (it lowers to a
    // fresh `Inst::Undef`), so any obligation depending on the referenced value stays
    // `unknown` and is never falsely proved. Mirrors the `&[&str]`/slice-table and
    // `&dyn Trait` opaque arms above.
    if matches!(ty.kind(), TyKind::Ref(..)) {
        return Operand::Constant(ConstValue::OpaqueConst);
    }

    // A bare (non-reference) INTEGER constant we could not evaluate above — a
    // const-generic param `N`, an associated const `T::LIMIT`, or `size_of::<T>()`
    // read inside a *generic* body where const-eval is unavailable (`try_to_bits`
    // returned `None` in the `Int`/`Uint` arms, and `const_operand_value` could not
    // produce a region-free valtree). The reference `OpaqueConst` rescue above is the
    // WRONG SORT here (it lowers to a fat-pointer `Undef`, but this value must keep an
    // INTEGER sort to stay well-typed under arithmetic/indexing). Degrade to a typed
    // opaque scalar carrying the integer width/signedness instead of poisoning the
    // whole function into Unsupported. Sound: every consumer lowers this to a FRESH
    // integer-sorted symbol that asserts no value, so value/div/index/equality
    // obligations over it stay `unknown`, never falsely proved (the div-zero and
    // const-eq folds in trust-vcgen treat it as unknown-valued, NOT known-nonzero or
    // known-unequal). Bare `bool` const-generics and associated-type-projection
    // (`Alias`) consts are deliberately NOT handled here: a `bool` needs a Bool sort
    // (not an integer one) and an `Alias` const has no resolved integer width at
    // extraction time, so both stay fail-closed below.
    match ty.kind() {
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            // Trust: piece #7a — a const-generic PARAM value (`N`) keeps its param
            // identity so it lowers to the SAME symbol the array length `[T; N]`
            // uses (via `const_param_symbol`), letting a guard `if i < N`
            // discharge `a[i]`. An assoc-const / `size_of` (no param identity)
            // stays the existing unconstrained `OpaqueScalar`.
            if let Some((index, name)) = const_param_identity(tcx, const_op) {
                return Operand::Constant(ConstValue::ConstParam {
                    index,
                    name,
                    width,
                    signed: true,
                });
            }
            return Operand::Constant(ConstValue::OpaqueScalar { width, signed: true });
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            // Trust: piece #7a — see the `Int` arm; the `usize` const-generic
            // length param `N` is the common case and lands here.
            if let Some((index, name)) = const_param_identity(tcx, const_op) {
                return Operand::Constant(ConstValue::ConstParam {
                    index,
                    name,
                    width,
                    signed: false,
                });
            }
            return Operand::Constant(ConstValue::OpaqueScalar { width, signed: false });
        }
        // A BOOL const-generic param (`const B: bool`, e.g. aterm-lz4's
        // `compress_internal::<_, USE_DICT, _>`). Encoded in-band as a
        // width-1 unsigned `ConstParam` — Rust has no 1-bit integer type, so
        // the pattern is unambiguous; trust-vcgen and trust-ir-bridge type it
        // `Bool` and lower it to the ONE shared Bool-sorted per-param symbol.
        // The shared symbol is the point: refusing here (the previous
        // fail-closed behavior) both blocked the native bundle for the whole
        // function AND left the v1 lane's occurrences as per-use havoc, whose
        // decorrelated `if B` guards minted spurious counterexamples on
        // dict-gated arithmetic. SOUND: the symbol asserts no value, so the
        // proof holds for both instantiations or not at all. Non-param bool
        // consts (assoc consts etc.) keep the fail-closed refusal below.
        TyKind::Bool => {
            if let Some((index, name)) = const_param_identity(tcx, const_op) {
                return Operand::Constant(ConstValue::ConstParam {
                    index,
                    name,
                    width: 1,
                    signed: false,
                });
            }
        }
        _ => {}
    }

    unsupported_operand(
        "Const",
        format!("unsupported constant of MIR type {ty:?}; refusing to prove with a guessed value"),
    )
}

/// Read the pointee bytes of an evaluated `&[u8; N]` constant.
///
/// A sized reference has scalar ABI, unlike `&str`/`&[u8]`, so rustc's
/// `try_get_slice_bytes_for_diagnostics` is intentionally invalid for this
/// representation. Accept only a provenance-bearing pointer to a global memory
/// allocation, require the exact `N`-byte range to be in bounds, initialized,
/// and free of nested pointer provenance, and otherwise return `None` so the
/// caller retains its opaque fail-closed fallback.
fn byte_array_ref_bytes_from_const_value(
    tcx: TyCtxt<'_>,
    value: mir::ConstValue,
    byte_len: u64,
) -> Option<Vec<u8>> {
    let mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(pointer, _)) = value else {
        return None;
    };
    let (provenance, offset) = pointer.prov_and_relative_offset();
    let allocation = tcx.global_alloc(provenance.alloc_id());
    let mir::interpret::GlobalAlloc::Memory(allocation) = allocation else {
        return None;
    };
    let size = rustc_abi::Size::from_bytes(byte_len);
    if offset.bytes().checked_add(byte_len)? > allocation.inner().size().bytes() {
        return None;
    }
    let range = mir::interpret::AllocRange { start: offset, size };
    allocation.inner().get_bytes_strip_provenance(&tcx, range).ok().map(<[u8]>::to_vec)
}

/// Trust: peel reference layers off a type-level constant and, if it ultimately
/// refers to `str`, `[u8]`, or `[u8; N]`, return its raw bytes. Mirrors rustc's
/// own `pretty_print_const_valtree` (rustc_middle/src/ty/print/pretty.rs): a
/// valtree is transparent across `&` layers, so the `&&str` const that
/// `x == "lit"` produces — by auto-ref'ing the literal to a promoted const —
/// carries the same byte-branch valtree as the inner `&str`. We re-type that one
/// valtree a layer at a time, delegating byte validation (including the
/// per-element u8 check) to `try_to_raw_bytes`, until it accepts. Only a `Branch`
/// valtree can hold element bytes; gating on it up front mirrors rustc's own
/// match and keeps `try_to_raw_bytes`' internal `to_branch()` away from a leaf.
/// Fail closed to `None` for any non-byte reference so we never feed downstream a
/// guessed value.
///
/// T7 (fmt-template bytes): the same peel-and-read also serves `&[u8; N]`
/// reference constants — the `format_args!` template arrays — whose valtrees are
/// byte branches exactly like a str's; the caller's Slice/Array arm gates on the
/// u8 element type before delegating here.
fn str_ref_bytes_from_value<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Value<'tcx>) -> Option<Vec<u8>> {
    value.try_to_branch()?;
    let mut ty = value.ty;
    for _ in 0..8 {
        if let Some(bytes) = (ty::Value { ty, valtree: value.valtree }).try_to_raw_bytes(tcx) {
            return Some(bytes.to_vec());
        }
        let ty::TyKind::Ref(_, inner, _) = ty.kind() else { return None };
        ty = *inner;
    }
    None
}

/// Trust (eq-guard channel): recover a promoted/const `&E` whose std-enum
/// pointee is a PAYLOAD-LESS variant (`&Option<T>::None`, a unit `&Result`
/// variant) as [`ConstValue::UnitVariantRef`]. Valtrees are transparent across
/// `&` (see [`str_ref_bytes_from_value`]), so the same valtree re-typed at the
/// pointee destructures directly. Fail-closed (`None`) for: a generic pointee,
/// a non-std enum, a payload-carrying value (`&Some(5)` — non-empty fields), or
/// a mutable reference.
fn std_enum_unit_variant_ref_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ty::Value<'tcx>,
) -> Option<ConstValue> {
    let ty::TyKind::Ref(_, inner, mutbl) = value.ty.kind() else {
        return None;
    };
    if mutbl.is_mut() || inner.has_non_region_param() {
        return None;
    }
    let ty::TyKind::Adt(adt_def, _) = inner.kind() else {
        return None;
    };
    if !adt_def.is_enum() {
        return None;
    }
    let enum_name = crate::safe_def_path_str(tcx, adt_def.did());
    if !matches!(
        enum_name.as_str(),
        "core::option::Option"
            | "std::option::Option"
            | "core::result::Result"
            | "std::result::Result"
    ) {
        return None;
    }
    let pointee = ty::Value { ty: *inner, valtree: value.valtree };
    let destructured = pointee.destructure_adt_const();
    if !destructured.fields.is_empty() {
        return None;
    }
    let variant = destructured.variant.as_usize();
    if !adt_def.variant(destructured.variant).fields.is_empty() {
        return None;
    }
    Some(ConstValue::UnitVariantRef { enum_name, variant })
}

/// Read a `&[&str; N]` / `&[&str]` format-template PIECES array and concatenate its literal
/// pieces into one byte string. This is THIS toolchain's `core::fmt::Arguments::new(pieces, args)`
/// template form — DISTINCT from the `&[u8; N]` compact byte template handled inline above — and
/// it was otherwise lost to `OpaqueConst`, blinding the trust-vcgen contract-panic matcher to
/// EVERY formatted `panic!("… {x} …")` message (so `#[trust::contract_panic]` could never excuse a
/// formatted intentional panic). SOUND: the result is emitted as `ConstValue::Str`, which the
/// bridge lowers to the SAME injectively-named OPAQUE symbol as `OpaqueConst` (contents never
/// content-asserted); the concatenated bytes are only ever `contains`-matched by the panic-message
/// matcher, never used as a value. The `{}` placeholders between pieces are simply dropped (the
/// pieces run together), which is exactly what the substring match needs.
fn str_pieces_ref_bytes_from_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ty::Value<'tcx>,
) -> Option<Vec<u8>> {
    // Peel `&[&str; N]` to the array/slice type; the valtree is transparent across `&` layers
    // (see `str_ref_bytes_from_value`), so the same valtree describes the array.
    let mut ty = value.ty;
    for _ in 0..8 {
        let ty::TyKind::Ref(_, inner, _) = ty.kind() else { break };
        ty = *inner;
    }
    let elem_ty = match ty.kind() {
        ty::TyKind::Array(elem, _) | ty::TyKind::Slice(elem) => *elem,
        _ => return None,
    };
    // Element must be `&str` — otherwise this is some other `&[T]` table, left opaque.
    let ty::TyKind::Ref(_, s, _) = elem_ty.kind() else { return None };
    if !matches!(s.kind(), ty::TyKind::Str) {
        return None;
    }
    let branch = (ty::Value { ty, valtree: value.valtree }).try_to_branch()?;
    let mut out = Vec::new();
    for child in branch {
        let piece = str_ref_bytes_from_value(tcx, child.try_to_value()?)?;
        out.extend_from_slice(&piece);
    }
    Some(out)
}

/// Read the bytes of a `&[u8; N]` (THIN array reference) `Const::Val` — this toolchain's
/// `core::fmt::Arguments::new(byte_template, args)` FORMAT TEMPLATE for a formatted
/// `panic!("… {x} …")`. `const_operand_value` returns `None` for `Const::Val` and the
/// existing valtree reader only handles the promoted (`Const::Unevaluated`) form, so a
/// directly-evaluated byte template was lost to `OpaqueConst`, blinding the contract-panic
/// matcher to the message. Read the `N` array bytes directly from the pointed-to allocation.
/// SOUND: emitted as an opaque `ConstValue::Str` (never content-asserted); diagnostics-only
/// alloc inspection, exact-or-`None`.
fn array_ref_u8_const_bytes<'tcx>(tcx: TyCtxt<'tcx>, c: &mir::Const<'tcx>) -> Option<Vec<u8>> {
    let mir::Const::Val(val, ref_ty) = c else { return None };
    let ty::TyKind::Ref(_, inner, _) = ref_ty.kind() else { return None };
    let ty::TyKind::Array(elem, len_const) = inner.kind() else { return None };
    if *elem != tcx.types.u8 {
        return None;
    }
    let len = len_const.try_to_target_usize(tcx)? as usize;
    let mir::ConstValue::Scalar(scalar) = val else { return None };
    let ptr = scalar.to_pointer(&tcx).discard_err()?;
    let (prov, offset) = ptr.into_pointer_or_addr().ok()?.prov_and_relative_offset();
    let alloc = tcx.global_alloc(prov.alloc_id()).unwrap_memory();
    let start = offset.bytes() as usize;
    let bytes = alloc
        .inner()
        .inspect_with_uninit_and_ptr_outside_interpreter(start..start.checked_add(len)?);
    Some(bytes.to_vec())
}

fn is_fieldless_singleton_struct_ty<'tcx>(ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() => adt_def.all_fields().next().is_none(),
        _ => false,
    }
}

fn unsupported_operand(kind: impl Into<String>, detail: String) -> Operand {
    Operand::Unsupported { kind: kind.into(), detail }
}

/// Reconstruct aggregate constants that optimized MIR collapses into
/// `Rvalue::Use(const ...)` so downstream passes still see tuple/ADT structure.
fn convert_const_aggregate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<Rvalue> {
    if let mir::Const::Val(value, ty) = const_op.const_ {
        if let Some(rvalue) = convert_mir_const_value_aggregate_rvalue(tcx, value, ty) {
            return Some(rvalue);
        }
    }

    let value = const_operand_value(tcx, const_op)?;

    match value.ty.kind() {
        ty::TyKind::Tuple(fields) => {
            if fields.is_empty() {
                return Some(Rvalue::Use(Operand::Constant(ConstValue::Unit)));
            }
            let ops = value
                .try_to_branch()?
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(AggregateKind::Tuple, ops))
        }
        ty::TyKind::Array(_, _) => {
            let ops = value
                .try_to_branch()?
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(AggregateKind::Array, ops))
        }
        ty::TyKind::Adt(adt_def, _) => {
            let destructured = value.destructure_adt_const();
            let ops = destructured
                .fields
                .iter()
                .map(|field| convert_ty_const_to_operand(tcx, *field))
                .collect::<Option<Vec<_>>>()?;
            Some(Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: crate::safe_def_path_str(tcx, adt_def.did()),
                    variant: destructured.variant.as_usize(),
                    active_field: None,
                    // Trust (C1): the const-destructure path does not carry the site's
                    // GenericArgs, so there is nothing faithful to record. `None` means "not
                    // known here", never "no generics" — a comparison must treat it as
                    // uninformative rather than as agreement.
                    args: None,
                },
                ops,
            ))
        }
        _ => None,
    }
}

/// Reconstruct one-level tuple/ADT constants materialized as `mir::Const::Val`.
///
/// Field operands still have to be scalar or unit; nested aggregate fields remain
/// unsupported because `trust-types::Operand` cannot encode them losslessly.
fn convert_mir_const_value_aggregate_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    ty: ty::Ty<'tcx>,
) -> Option<Rvalue> {
    if ty.has_non_region_param() {
        return None;
    }

    let contents = tcx.try_destructure_mir_constant_for_user_output(value, ty)?;
    let ops = contents
        .fields
        .iter()
        .map(|(field_value, field_ty)| {
            convert_mir_const_value_to_operand(tcx, *field_value, *field_ty)
        })
        .collect::<Option<Vec<_>>>()?;

    match ty.kind() {
        ty::TyKind::Tuple(fields) => {
            if fields.is_empty() {
                return Some(Rvalue::Use(Operand::Constant(ConstValue::Unit)));
            }
            Some(Rvalue::Aggregate(AggregateKind::Tuple, ops))
        }
        ty::TyKind::Adt(adt_def, adt_args) => Some(Rvalue::Aggregate(
            AggregateKind::Adt {
                name: crate::safe_def_path_str(tcx, adt_def.did()),
                variant: contents.variant?.as_usize(),
                active_field: None,
                // Trust (C1): the args ARE in hand here, so record them.
                args: Some(crate::safe_def_path_str_with_args(tcx, adt_def.did(), adt_args)),
            },
            ops,
        )),
        _ => None,
    }
}

fn const_operand_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<ty::Value<'tcx>> {
    match const_op.const_ {
        mir::Const::Ty(_, ty_const) => ty_const.try_to_value(),
        mir::Const::Unevaluated(unevaluated, ty) => {
            if ty.has_non_region_param() || unevaluated.args.has_non_region_param() {
                return None;
            }
            let typing_env = ty::TypingEnv::fully_monomorphized();
            // Associated consts over projected associated types can remain
            // unnormalizable in generic MIR. Treat them as unavailable instead
            // of forcing codegen-style resolution before monomorphization.
            if unevaluated.args.has_non_region_param() || ty.has_non_region_param() {
                return None;
            }
            let args = tcx
                .try_normalize_erasing_regions(
                    typing_env,
                    ty::Unnormalized::new_wip(unevaluated.args),
                )
                .ok()?;
            if args.has_non_region_param() {
                return None;
            }
            let instance =
                ty::Instance::try_resolve(tcx, typing_env, unevaluated.def, args).ok().flatten()?;
            let valtree = tcx
                .const_eval_global_id_for_typeck(
                    typing_env,
                    rustc_middle::mir::interpret::GlobalId {
                        instance,
                        promoted: unevaluated.promoted,
                    },
                    const_op.span,
                )
                .ok()?
                .ok()?;
            Some(ty::Value { ty, valtree })
        }
        mir::Const::Val(_, _) => None,
    }
}

/// Read a scalar valtree leaf as a typed `ConstValue` (`idx_ty` gives the sign/width).
/// Returns None for anything not a plain integer leaf — fail-closed (never a guessed
/// bound), so the caller leaves the `contains` call opaque instead of a wrong bound.
fn scalar_valtree_to_const_value<'tcx>(
    c: ty::Const<'tcx>,
    idx_ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ConstValue> {
    let leaf = c.try_to_leaf()?;
    match idx_ty.kind() {
        ty::TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            let bits = leaf.to_bits(size);
            Some(ConstValue::Int(size.sign_extend(bits) as i128))
        }
        ty::TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let size = rustc_abi::Size::from_bits(width as u64);
            Some(ConstValue::Uint(leaf.to_bits(size), width))
        }
        _ => None,
    }
}

/// `(start, end)` const values of a `Range<Idx>` / `RangeInclusive<Idx>` compile-time
/// constant, read from its valtree (`Branch([start, end, ..])`). None unless both are
/// integer leaves of the recovered `Idx` type — fail-closed.
fn range_const_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    const_op: &mir::ConstOperand<'tcx>,
) -> Option<(ConstValue, ConstValue)> {
    let value = const_operand_value(tcx, const_op)?;
    // `contains` takes `&self`, so the const is `&Range<Idx>` — peel references
    // (the valtree is transparent across `&`) to reach the Range adt and its `Idx`.
    let mut adt_ty = value.ty;
    while let ty::TyKind::Ref(_, inner, _) = adt_ty.kind() {
        adt_ty = *inner;
    }
    let idx_ty = match adt_ty.kind() {
        ty::TyKind::Adt(_, args) => args.type_at(0),
        _ => return None,
    };
    let branch = value.valtree.try_to_branch()?;
    if branch.len() < 2 {
        return None;
    }
    let start = scalar_valtree_to_const_value(branch[0], idx_ty, tcx);
    let end = scalar_valtree_to_const_value(branch[1], idx_ty, tcx);
    Some((start?, end?))
}

/// The UNIQUE whole-local definition of `local`, or None if it has zero or multiple
/// assignments (ambiguous — fail-closed, never a guessed value).
fn unique_whole_local_def<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    local: mir::Local,
) -> Option<&'a mir::Rvalue<'tcx>> {
    let mut found = None;
    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let mir::StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind {
                if lhs.local == local && lhs.projection.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rvalue);
                }
            }
        }
    }
    found
}

/// The whole-local of an operand, hopping through `Use(copy/move)` chains, or None.
fn whole_local_through_copies<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    mut local: mir::Local,
) -> Option<(mir::Local, &'a mir::Rvalue<'tcx>)> {
    for _ in 0..16 {
        let def = unique_whole_local_def(mir_body, local)?;
        match def {
            mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                if p.projection.is_empty() =>
            {
                local = p.local;
            }
            other => return Some((local, other)),
        }
    }
    None
}

fn operand_whole_local(arg: &mir::Operand<'_>) -> Option<mir::Local> {
    match arg {
        mir::Operand::Copy(p) | mir::Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The range arg is a const, spelled `_t = const promoted[..]; contains(move _t, ..)`.
/// Trace through copy chains to the constant. None unless it resolves to one.
fn trace_operand_to_const<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    arg: &'a mir::Operand<'tcx>,
) -> Option<&'a mir::ConstOperand<'tcx>> {
    if let mir::Operand::Constant(box c) = arg {
        return Some(c);
    }
    let (_, def) = whole_local_through_copies(mir_body, operand_whole_local(arg)?)?;
    match def {
        mir::Rvalue::Use(mir::Operand::Constant(box c), _) => Some(c),
        _ => None,
    }
}

/// `contains` takes `&x`; trace the reference (through copy chains) to its pointee `x`
/// so the synthesized bound constrains the actual variable. None on any other shape.
fn contains_value_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    arg: &mir::Operand<'tcx>,
) -> Option<Operand> {
    let (_, def) = whole_local_through_copies(mir_body, operand_whole_local(arg)?)?;
    match def {
        // Trust: M6 rung-7 sweep — `mir_body` is a real compiled body, so use its
        // own `typing_env` for the pointee place's projection types, same as
        // `extract_body`'s locals.
        mir::Rvalue::Ref(_, _, pointee) => {
            Some(Operand::Copy(convert_place(tcx, pointee, Some(mir_body.typing_env(tcx)))))
        }
        _ => None,
    }
}

/// Rewrite `r = <Range|RangeInclusive>::contains(const_range, &x)` into native
/// comparisons `r = (x >= start) & (x <(=) end)`, so a `(L..=U).contains(&x)` input-
/// validation guard establishes `L <= x <= U` for the guarded arithmetic that follows.
/// SOUND: exactly `contains`' semantics; bounds are read from the range's compile-time
/// constant valtree (type-aware); any range/value we cannot read precisely is left as
/// the original opaque call (fail-closed — never a wrong bound). Only const ranges are
/// rewritten (the dominant idiom, e.g. `(0..=9999).contains(&year)`).
pub(crate) fn rewrite_range_contains_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    let mut next_local = vbody.locals.iter().map(|l| l.index).max().map_or(0, |m| m + 1);

    // SOUNDNESS-CRITICAL precompute (verdict-identical to the former per-call scan):
    // collect ONCE the set of every local that is mutably borrowed anywhere in the
    // body — i.e. appears as `place.local` in a `Ref{mutable:true}` or any `AddressOf`
    // (raw `&raw const`/`&raw mut`, matching the original `AddressOf(_, place)` which
    // ignored the mutability bool). This MUST scan the SAME scope (all blocks, all
    // stmts of `vbody`) with the SAME predicate as the staleness gate below, so the
    // skip decision is byte-for-byte identical for every call: membership `vl ∈ set`
    // ⟺ `∃ stmt` matching the predicate with `place.local == vl`. Replaces the
    // O(calls × stmts) rescan with one O(stmts) pass + O(1) lookups; the gate that
    // backs the range-contains &mut staleness fix is unchanged in semantics.
    let mut_borrowed_locals: std::collections::HashSet<usize> = vbody
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s {
            Statement::Assign { rvalue: Rvalue::Ref { mutable: true, place }, .. } => {
                Some(place.local)
            }
            Statement::Assign { rvalue: Rvalue::AddressOf(_, place), .. } => Some(place.local),
            _ => None,
        })
        .collect();

    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
            &bb_data.terminator().kind
        else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let name = func_operand_name(tcx, func);
        if !name.ends_with("::contains") {
            continue;
        }
        let inclusive = name.contains("RangeInclusive");
        let exclusive = !inclusive && name.contains("ops::") && name.contains("Range");
        if !(inclusive || exclusive) {
            continue;
        }
        let Some(const_op) = trace_operand_to_const(mir_body, &args[0].node) else { continue };
        let Some((start_cv, end_cv)) = range_const_bounds(tcx, const_op) else { continue };
        let Some(value_op) = contains_value_operand(tcx, mir_body, &args[1].node) else { continue };

        // SOUNDNESS (hunt-13): do NOT synthesize the range guard when the validated
        // value's local is MUTABLY BORROWED anywhere in the body. Otherwise
        // `(0..=4).contains(&x); let p = &mut x; *p = b; arr[x]` carries the STALE
        // `x <= 4` range fact across the `*p = b` Deref-store (which is NOT a
        // whole-local definition of `x`, so the single-definition gate that backs this
        // rewrite never sees it) straight into a kernel-CERTIFIED out-of-bounds proof.
        // Mirrors the `Ref{mutable}`/`AddressOf` staleness gate the comparison-guard
        // lane already applies (hunt-5/7/8/9). Conservative: whole-body, on the base
        // local; leaves the opaque `contains` call (fail-closed) for a mutated value.
        if let Operand::Copy(p) | Operand::Move(p) = &value_op {
            // O(1) lookup into the once-computed set; membership is identical to the
            // former per-call `any(..)` scan (same scope, same predicate). See the
            // precompute above for the soundness argument.
            if mut_borrowed_locals.contains(&p.local) {
                continue;
            }
        }

        let block = &mut vbody.blocks[bb.as_usize()];
        let span = SourceSpan::default();
        let t1 = next_local;
        let t2 = next_local + 1;
        next_local += 2;
        vbody.locals.push(LocalDecl { index: t1, ty: Ty::Bool, name: None });
        vbody.locals.push(LocalDecl { index: t2, ty: Ty::Bool, name: None });
        block.stmts.push(Statement::Assign {
            place: Place::local(t1),
            rvalue: Rvalue::BinaryOp(BinOp::Ge, value_op.clone(), Operand::Constant(start_cv)),
            span: span.clone(),
        });
        block.stmts.push(Statement::Assign {
            place: Place::local(t2),
            rvalue: Rvalue::BinaryOp(
                if inclusive { BinOp::Le } else { BinOp::Lt },
                value_op,
                Operand::Constant(end_cv),
            ),
            span: span.clone(),
        });
        block.stmts.push(Statement::Assign {
            place: convert_place(tcx, destination, Some(mir_body.typing_env(tcx))),
            rvalue: Rvalue::BinaryOp(
                BinOp::BitAnd,
                Operand::Copy(Place::local(t1)),
                Operand::Copy(Place::local(t2)),
            ),
            span,
        });
        block.terminator = Terminator::Goto(BlockId(target.as_usize()));
    }
}

/// What a value-preserving backward trace from a checked address discovered about
/// its allocation. `Some` means the address provably originates from an INFALLIBLE
/// box allocation (`Box::new*` / box-new lang item) — i.e. a non-null pointer
/// whose base is `align`-aligned (when the box pointee's layout was recoverable).
struct BoxAllocFacts {
    /// `align_of` of the box pointee (bytes), or `None` if no `Box<P>`-typed local
    /// was crossed (e.g. a raw `box_new_uninit` whose `*mut u8` result never got a
    /// `Box<…>` type before the address was taken). `None` ⇒ alignment unknown ⇒
    /// a misalign assert is NOT discharged (fail-closed); null still is.
    align: Option<u64>,
}

/// Is `name` a call to an INFALLIBLE box allocator — one that aborts (never returns)
/// on OOM and yields a non-null, `align_of::<pointee>()`-aligned pointer? These are
/// `Box::<T>::new` / `::new_uninit` / `::new_zeroed` and the `box_new_uninit` /
/// `exchange_malloc` lang items. CRITICALLY EXCLUDES `alloc::alloc` and friends,
/// which are FALLIBLE (may return null) — discharging a null/misalign check on a
/// fallible allocation would be a false PROVE.
fn is_infallible_box_allocator(name: &str) -> bool {
    // STD-ORIGIN GATE (defense-in-depth, mirrors the validated
    // `sep_engine::is_known_good_box_alloc`): the real `Box` is defined in `alloc`
    // (re-exported in `std`); its monomorphized callee path renders with one of
    // these crate prefixes. Requiring it means a USER type `mycrate::boxed::Box`
    // with a `::new` method CANNOT masquerade as the infallible std box allocator —
    // closing the "loose substring gate" hazard the soundness review flagged
    // (fixture N1). Without this, N1 is sound only by the value-preserving trace's
    // fail-closed shape; with it, the recogniser itself rejects the impostor.
    let std_origin =
        name.starts_with("std::") || name.starts_with("alloc::") || name.starts_with("core::");
    if !std_origin {
        return false;
    }
    // The turbofish on the method form is a MIDDLE turbofish
    // (`std::boxed::Box::<[T; N]>::new_uninit`), so the `::new*` tail is clean.
    let boxed_method = name.contains("boxed::Box")
        && (name.ends_with("::new")
            || name.ends_with("::new_uninit")
            || name.ends_with("::new_zeroed"));
    boxed_method || name.ends_with("box_new_uninit") || name.ends_with("exchange_malloc")
}

/// Find the UNIQUE `Call` terminator whose destination is the whole local `local`
/// (no projection). `None` if there is no such call or more than one (ambiguous —
/// fail-closed). Complements `unique_whole_local_def`, which only sees `Assign`
/// statements; an allocator result is a `Call` destination, never an `Assign`.
fn unique_call_def_for_local<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    local: mir::Local,
) -> Option<&'a mir::TerminatorKind<'tcx>> {
    let mut found = None;
    for bb_data in mir_body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            if destination.local == local && destination.projection.is_empty() {
                if found.is_some() {
                    return None;
                }
                found = Some(&bb_data.terminator().kind);
            }
        }
    }
    found
}

/// Trace the checked address `addr_local` BACKWARD through ONLY value-preserving
/// pointer operations to a recognized INFALLIBLE box allocation, returning the
/// allocation's facts (non-null always; alignment when a `Box<P>` type was crossed).
///
/// SOUNDNESS — this is the gate that makes assert discharge a false-PROVE-free
/// dead-check elimination. EVERY hop must leave the address bits UNCHANGED:
///   * `Use(copy/move)` of a whole local,
///   * an address-preserving cast (`PtrToPtr` / `Transmute` / ptr↔int provenance
///     casts / `MutToConst`/`ArrayToPointer` coercions) whose SOURCE operand is a
///     pointer (so a value transmute like `f64→u64` is rejected) and whose place
///     projects ONLY through transparent newtype fields (Box→Unique→NonNull),
///   * bottoming out at an infallible box allocator `Call`.
/// Pointer ARITHMETIC (offset/add), an unknown rvalue, multiple defs, a projected
/// `found`, or a fallible/non-box allocator all break the chain → `None` → the
/// assert is KEPT. A wrong success here would be the sacred violation, so the
/// recogniser is deliberately narrow.
/// In-body INFALLIBLE box-allocation trace. Reads alignment from the allocator CALL's
/// own `T` (immune to a chain `Box<P>` relabel). Returns `None` for a RECEIVED box (no
/// allocator call in this body) — the gap the `box_alloc_facts_for_addr` wrapper now
/// fills via `received_box_facts`.
fn alloc_call_box_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mir_body: &mir::Body<'tcx>,
    addr_local: mir::Local,
) -> Option<BoxAllocFacts> {
    let mut local = addr_local;
    for _ in 0..16 {
        // Statement (`Assign`) def: value-preserving hops only.
        if let Some(def) = unique_whole_local_def(mir_body, local) {
            // SOUNDNESS (mixed-def guard — closes a verified pre-existing false PROVE):
            // a local defined by BOTH an `Assign` and a terminator (`Call`/`Yield`/
            // `InlineAsm`) is ambiguous. `unique_whole_local_def` sees only the `Assign`
            // and is blind to the terminator def, which on another CFG path can be a
            // fallible `Box::from_raw(alloc(..))` reaching the SAME deref. Trusting the
            // `Assign` hop past that would discharge a genuinely-faulting deref. Bail.
            if local_has_terminator_def(mir_body, local) {
                return None;
            }
            match def {
                mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                    if p.projection.is_empty() =>
                {
                    local = p.local;
                    continue;
                }
                mir::Rvalue::Cast(
                    kind,
                    operand @ (mir::Operand::Copy(p) | mir::Operand::Move(p)),
                    _,
                ) if cast_is_address_preserving(*kind)
                    && p.projection.iter().all(|e| matches!(e, mir::PlaceElem::Field(..)))
                    && source_is_pointer_like(tcx, operand.ty(&mir_body.local_decls, tcx)) =>
                {
                    local = p.local;
                    continue;
                }
                // Any other rvalue (pointer arithmetic, aggregate, unknown) — stop.
                _ => return None,
            }
        }

        // Otherwise the local must be defined by a `Call`; only an infallible box
        // allocator bottoms out the trace. The allocation alignment is read from the
        // ALLOCATOR CALL's own type argument — the TRUE allocated type — NOT from any
        // `Box<P>` label crossed in the chain. CRITICAL SOUNDNESS: a transmute can
        // FALSIFY the chain's `Box` label (`transmute::<Box<u8>, Box<u128>>(b)` makes a
        // `Box<u128>`-typed local over an align-1 allocation), so trusting the label
        // would discharge a genuinely-misaligned `u128` deref — a false PROVE. The
        // allocator call's `T` is immune to that lie.
        if let Some(mir::TerminatorKind::Call { func, .. }) =
            unique_call_def_for_local(mir_body, local)
        {
            let name = func_operand_name(tcx, func);
            if is_infallible_box_allocator(&name) {
                return Some(BoxAllocFacts {
                    align: box_allocator_alignment(tcx, typing_env, func),
                });
            }
        }
        return None;
    }
    None
}

/// Facts about the allocation a checked address points into. Tries the in-body infallible-
/// allocator trace first (align from the allocator's `T`); falls back to a box RECEIVED
/// from the caller (a `Box`/`&` parameter, or a field/deref of one). Same name/signature
/// as before, so the two discharge sites are unchanged.
fn box_alloc_facts_for_addr<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mir_body: &mir::Body<'tcx>,
    addr_local: mir::Local,
) -> Option<BoxAllocFacts> {
    if let Some(facts) = alloc_call_box_facts(tcx, typing_env, mir_body, addr_local) {
        return Some(facts);
    }
    received_box_facts(tcx, typing_env, mir_body, addr_local)
}

/// Does ANY terminator define the WHOLE local `local` — a `Call` destination, a `Yield`
/// resume place, or an `InlineAsm` output? MIR locals are NOT SSA: a local can be
/// `Assign`-defined on one path and terminator-defined on another; `unique_whole_local_def`
/// (statements only) is blind to the latter. Any received-box hop that trusts a single
/// `Assign` MUST reject such a local (fail-closed superset), else an invisible
/// `Box::from_raw(alloc(..))` def yields a false PROVE. Also the mixed-def guard for the
/// Os-provenance trace: an `Assign`+`Call`-defined local is ambiguous there for the same
/// reason, so that trace fails CLOSED on it too.
fn local_has_terminator_def(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    mir_body.basic_blocks.iter().any(|bb| match &bb.terminator().kind {
        mir::TerminatorKind::Call { destination, .. } => {
            destination.local == local && destination.projection.is_empty()
        }
        mir::TerminatorKind::Yield { resume_arg, .. } => {
            resume_arg.local == local && resume_arg.projection.is_empty()
        }
        mir::TerminatorKind::InlineAsm { operands, .. } => operands.iter().any(|op| {
            matches!(op,
                mir::InlineAsmOperand::Out { place: Some(p), .. }
                | mir::InlineAsmOperand::InOut { out_place: Some(p), .. }
                if p.local == local && p.projection.is_empty())
        }),
        _ => false,
    })
}

/// Fallback for a box RECEIVED from the caller (no in-body allocator call). Walk the
/// checked address backward through the SAME value-preserving hops as `alloc_call_box_facts`
/// until we reach the `ElaborateBoxDerefs` box-deref source `<box>.0:Unique.0:NonNull`,
/// which the optimizer exposes EITHER as a `Transmute` source (box copied to a local;
/// mir-opt-level<=1) OR as a bare-NonNull-temp `Use` source (box read through a reference;
/// mir-opt-level>=2). Both bottom out via `synth_box_facts`.
fn received_box_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mir_body: &mir::Body<'tcx>,
    addr_local: mir::Local,
) -> Option<BoxAllocFacts> {
    let mut local = addr_local;
    for _ in 0..16 {
        // Mixed-def guard on every address-trace local (defense in depth; these are
        // normally single-def instrumentation temps).
        if local_has_terminator_def(mir_body, local) {
            return None;
        }
        let def = unique_whole_local_def(mir_body, local)?;
        match def {
            // THE box-deref source `<box>.0:Unique.0:NonNull`, via a `Transmute` (Shape A)
            // OR a `Use` (Shape B). MUST be tried before the generic cast/copy hops so we
            // stop at the box base instead of hopping past it (its projection is all-`Field`
            // and NonNull is pointer-like, so the generic arms would otherwise consume it).
            mir::Rvalue::Cast(
                mir::CastKind::Transmute,
                mir::Operand::Copy(p) | mir::Operand::Move(p),
                _,
            )
            | mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                if is_synth_box_deref_src(tcx, mir_body, p) =>
            {
                return synth_box_facts(tcx, typing_env, mir_body, p);
            }
            // Whole-local copy hop.
            mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                if p.projection.is_empty() =>
            {
                local = p.local;
            }
            // Address-preserving instrumentation cast hop (`_p as *const ()`, `.. as usize`).
            mir::Rvalue::Cast(
                kind,
                operand @ (mir::Operand::Copy(p) | mir::Operand::Move(p)),
                _,
            ) if cast_is_address_preserving(*kind)
                && p.projection.iter().all(|e| matches!(e, mir::PlaceElem::Field(..)))
                && source_is_pointer_like(tcx, operand.ty(&mir_body.local_decls, tcx)) =>
            {
                local = p.local;
            }
            _ => return None,
        }
    }
    None
}

/// Facts for a received box-deref whose source place is `src` (`<box>.0:Unique.0:NonNull`).
/// NULL is discharged (return `Some`) whenever the box provably ROOTS at a validity-
/// guaranteed received input — non-null then holds by the validity invariant, EVEN across
/// an in-body relabel (a transmute preserves the non-null address bits). MISALIGN
/// (`align = Some`) is discharged additionally ONLY when NO relabel was crossed and the
/// genuine box pointee `P` is concrete, so `align_of::<P>()` read from the OWNED-BOX BASE is
/// the true allocation alignment; the discharge site then requires `align_of::<P>() >= req`.
///
/// The transmute DST type is deliberately NOT inspected — `P` from the base plus the
/// discharge site's `>= req` gate is self-defending (a deref wanting higher alignment than
/// the base pointee provides keeps its check), which also makes this shape-agnostic across
/// the `Transmute→*const P` (Shape A) and `Use→NonNull temp` (Shape B) forms.
fn synth_box_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mir_body: &mir::Body<'tcx>,
    src: &mir::Place<'tcx>,
) -> Option<BoxAllocFacts> {
    let n = src.projection.len();
    let base_proj = &src.projection[..n - 2]; // n >= 2 guaranteed by synth_box_pointee
    let pointee = synth_box_pointee(tcx, mir_body, src)?; // P = base.boxed_ty()

    let relabeled = received_box_origin(tcx, mir_body, src.local, base_proj, 16)?;

    let align = if !relabeled && !pointee.has_non_region_param() {
        tcx.layout_of(typing_env.as_query_input(pointee)).ok().map(|l| l.align.abi.bytes())
    } else {
        None
    };
    Some(BoxAllocFacts { align })
}

/// True iff `src` is the SOURCE of an `ElaborateBoxDerefs` box-deref
/// (`<owned_box_place>.0:Unique.0:NonNull`).
fn is_synth_box_deref_src<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    src: &mir::Place<'tcx>,
) -> bool {
    synth_box_pointee(tcx, mir_body, src).is_some()
}

/// The genuine box pointee `P` (`= base.boxed_ty()`) of an `ElaborateBoxDerefs` box-deref
/// source `<owned_box_place>.0:Unique.0:NonNull`, or `None` if `src` is not that shape.
/// Mirrors `is_synth_box_ptr` (rustc_mir_transform/src/trust_verify.rs, committed
/// 885142823e): last two projections `Field(0): ptr::Unique<_>` then `Field(0):
/// ptr::NonNull<_>` (adt-def identity resolved from the `owned_box` lang item — a user
/// `myptr::Unique` cannot masquerade), base is an `owned_box`. `P` is read from the base,
/// never a relabeled far end.
fn synth_box_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    src: &mir::Place<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    let owned_box_did = tcx.lang_items().owned_box()?;
    let unique_did = tcx.adt_def(owned_box_did).non_enum_variant().fields.iter().next()?.did;
    let unique_def =
        tcx.type_of(unique_did).instantiate_identity().skip_normalization().ty_adt_def()?;
    let nonnull_did = unique_def.non_enum_variant().fields.iter().next()?.did;
    let nonnull_def =
        tcx.type_of(nonnull_did).instantiate_identity().skip_normalization().ty_adt_def()?;

    let proj = src.projection;
    let n = proj.len();
    if n < 2 {
        return None;
    }
    let mir::PlaceElem::Field(uq_idx, uq_ty) = proj[n - 2] else { return None };
    let mir::PlaceElem::Field(nn_idx, nn_ty) = proj[n - 1] else { return None };
    if uq_idx.as_u32() != 0 || nn_idx.as_u32() != 0 {
        return None;
    }
    if uq_ty.ty_adt_def() != Some(unique_def) || nn_ty.ty_adt_def() != Some(nonnull_def) {
        return None;
    }
    mir::Place::ty_from(src.local, &proj[..n - 2], &mir_body.local_decls, tcx).ty.boxed_ty()
}

/// Does the box VALUE named by `Place { base_local, base_proj }` provably ROOT at a
/// validity-guaranteed received input (a `Box`/`&` PARAMETER) reached by a safe access
/// path, crossing NO raw-pointer/union read and NO in-body allocation/`from_raw`?
/// `Some(relabeled)`: `relabeled` iff an address-preserving (potentially align-changing)
/// pointee cast was crossed; `None` if not so rooted (assert KEPT).
///
/// SOUNDNESS: a `Box<T>`/`&T` parameter is non-null and points to an `align_of::<T>()`-
/// aligned, live `T` by the caller's validity obligation — the SAME invariant rustc trusts
/// (no null/align check for a `&T` deref) and trust's sep-engine already relies on for ref
/// params (sep_engine.rs:957,967-988,2350-2366). A raw-pointer deref, a union field read,
/// or an in-body `from_raw`/alloc carries no such guarantee → `None`.
fn received_box_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    base_local: mir::Local,
    base_proj: &[mir::PlaceElem<'tcx>],
    fuel: u32,
) -> Option<bool> {
    if fuel == 0 || !box_place_safe_access_path(tcx, mir_body, base_local, base_proj) {
        return None;
    }
    origin_of_box_local(tcx, mir_body, base_local, fuel)
}

fn origin_of_box_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    local: mir::Local,
    fuel: u32,
) -> Option<bool> {
    if fuel == 0 || local_has_terminator_def(mir_body, local) {
        return None;
    }
    match unique_whole_local_def(mir_body, local) {
        // No whole-local `Assign` def. Sound ONLY for a PRISTINE (never whole-reassigned,
        // never terminator-defined) validity-guaranteed PARAMETER.
        None => (is_mir_parameter(mir_body, local)
            && !local_has_whole_assign(mir_body, local)
            && type_is_validity_nonnull(mir_body.local_decls[local].ty))
        .then_some(false),
        // The box VALUE is named by place `p` — a whole local, OR a projected safe access
        // path such as `(*_4)` / `((*_1) as Add).0`. Recurse THROUGH the access path.
        Some(mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _))
        | Some(mir::Rvalue::CopyForDeref(p)) => {
            received_box_origin(tcx, mir_body, p.local, p.projection, fuel - 1)
        }
        // `&place` — a reference of a genuine place is non-null; recurse into `place`.
        Some(mir::Rvalue::Ref(_, _, place)) => {
            received_box_origin(tcx, mir_body, place.local, place.projection, fuel - 1)
        }
        // Address-preserving pointee cast (possible RELABEL). Hop; mark `relabeled` (kills
        // misalign; null survives — address bits preserved, root non-null). Validate the
        // source access path too (rejects a union/raw-ptr relabel source for the null lane).
        Some(mir::Rvalue::Cast(
            kind,
            operand @ (mir::Operand::Copy(p) | mir::Operand::Move(p)),
            _,
        )) if cast_is_address_preserving(*kind)
            && p.projection.iter().all(|e| matches!(e, mir::PlaceElem::Field(..)))
            && source_is_pointer_like(tcx, operand.ty(&mir_body.local_decls, tcx)) =>
        {
            received_box_origin(tcx, mir_body, p.local, p.projection, fuel - 1).map(|_| true)
        }
        _ => None,
    }
}

/// Every `Deref` in `proj` must dereference a REFERENCE (`&T`) — never a raw pointer (no
/// validity guarantee) or a box (that IS the deref we discharge); every `Field` must NOT
/// read through a UNION (a union field carries no validity guarantee — its bytes could
/// form a null/misaligned pointer); only `Field`/`Downcast` otherwise. `Downcast` is
/// validity-safe: rustc emits it only discriminant-dominated, from match lowering.
fn box_place_safe_access_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    base_local: mir::Local,
    proj: &[mir::PlaceElem<'tcx>],
) -> bool {
    for (i, elem) in proj.iter().enumerate() {
        let base_ty = mir::Place::ty_from(base_local, &proj[..i], &mir_body.local_decls, tcx).ty;
        match elem {
            mir::PlaceElem::Deref => {
                if !base_ty.is_ref() {
                    return false;
                }
            }
            mir::PlaceElem::Field(..) => {
                if base_ty.is_union() {
                    return false;
                }
            }
            mir::PlaceElem::Downcast(..) => {}
            _ => return false,
        }
    }
    true
}

/// A valid PARAMETER of this type is non-null and points to a genuinely-typed,
/// `align_of::<pointee>()`-aligned pointee: a reference or a `Box`. Raw-pointer params are
/// EXCLUDED (no such guarantee).
fn type_is_validity_nonnull(ty: ty::Ty<'_>) -> bool {
    ty.is_ref() || ty.is_box()
}

/// Is `local` a function PARAMETER (`_1..=_arg_count`)?
fn is_mir_parameter(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    let i = local.as_usize();
    i >= 1 && i <= mir_body.arg_count
}

/// Does any statement assign the WHOLE local (used to reject a reassigned parameter).
fn local_has_whole_assign(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    mir_body.basic_blocks.iter().any(|bb| {
        bb.statements.iter().any(|s| {
            matches!(&s.kind, mir::StatementKind::Assign(box (lhs, _))
                if lhs.local == local && lhs.projection.is_empty())
        })
    })
}

/// The alignment (bytes) of the type an infallible box allocator allocates, read from
/// the allocator CALL's first type argument `T` — `Box::<T>::new`/`new_uninit`/
/// `new_zeroed` allocate `T` / `MaybeUninit<T>`, both `align_of::<T>()`-aligned. This
/// is the AUTHORITATIVE allocation alignment, immune to any chain `Box<P>` transmute
/// relabel. `None` for the free `box_new_uninit` (a `*mut u8` lang item with no type
/// argument), a still-generic `T`, or a layout error — then the misalign discharge is
/// withheld (fail-closed), while a null discharge (non-null is allocator-guaranteed)
/// can still proceed.
fn box_allocator_alignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    func: &mir::Operand<'tcx>,
) -> Option<u64> {
    let mir::Operand::Constant(box c) = func else {
        return None;
    };
    let ty::FnDef(_, generic_args) = c.const_.ty().kind() else {
        return None;
    };
    let elem = generic_args.types().next()?;
    if elem.has_non_region_param() {
        return None; // generic allocation — alignment is instantiation-dependent
    }
    let layout = tcx.layout_of(typing_env.as_query_input(elem)).ok()?;
    Some(layout.align.abi.bytes())
}

/// A cast SOURCE whose VALUE is a pointer/address, so an address-preserving cast off
/// it stays on the (box's) base address: a raw pointer, reference, or `Box`, plus the
/// std pointer-newtypes `NonNull` / `Unique` that the `Box` deref machinery projects
/// and transmutes through (`((box.0: Unique).0: NonNull) as *const _`). These wrappers
/// are NOT `is_any_ptr()` (they are structs), yet their value IS the contained pointer,
/// so the transmute is address-preserving. Anchored to the `ptr::` module path so a
/// value-struct / scalar `Transmute` (e.g. `f64`/`u64` → ptr) is still rejected —
/// without this gate a value reinterpretation could be mistaken for an address hop.
fn source_is_pointer_like<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.is_any_ptr() || ty.is_box() {
        return true;
    }
    if let Some(adt) = ty.ty_adt_def() {
        let path = crate::safe_def_path_str(tcx, adt.did());
        return path.contains("ptr::NonNull") || path.contains("ptr::Unique");
    }
    false
}

/// Address-preserving casts: the destination's address bits equal the source's.
/// (`IntToInt` is excluded — it may truncate; only pointer/provenance relabelings.)
fn cast_is_address_preserving(kind: mir::CastKind) -> bool {
    matches!(
        kind,
        mir::CastKind::PtrToPtr
            | mir::CastKind::Transmute
            | mir::CastKind::PointerExposeProvenance
            | mir::CastKind::PointerWithExposedProvenance
            | mir::CastKind::PointerCoercion(
                PointerCoercion::MutToConstPointer | PointerCoercion::ArrayToPointer,
                _,
            )
    )
}

/// For a `NullPointerDereference` assert (whose `AssertKind` carries NO operand),
/// recover the checked address local from the condition `cond`. rustc's null check
/// (`compiler/rustc_mir_transform/src/check_null.rs`) is
/// `is_ok = Not(BitAnd(is_null, should_check))` with `is_null = Eq(addr, 0)` and
/// `should_check = Ne(SizeOf, 0)`; in the verifier's `optimized_mir` the `SizeOf`
/// stays an UNEVALUATED const so the `BitAnd` is NOT folded away (a fully-folded
/// `Not(Eq(addr, 0))` is the degenerate ZST/const-size case). Recurse `cond` through
/// `Not` / `Use` / `BitAnd` to the `is_null` comparison `Eq(addr, 0)` and return
/// `addr`'s whole local. SOUNDNESS: the address is extracted ONLY from the `is_null`
/// `Eq(_, 0)` (the operand the null check actually tests), never from the
/// `should_check` `Ne(SizeOf, 0)` — so a non-address operand can't be mistaken for the
/// pointer. `None` on any other shape (fail-closed: assert KEPT).
fn null_check_addr_local<'tcx>(
    mir_body: &mir::Body<'tcx>,
    cond: &mir::Operand<'tcx>,
) -> Option<mir::Local> {
    null_check_addr_rec(mir_body, operand_whole_local(cond)?, 8)
}

fn null_check_addr_rec<'tcx>(
    mir_body: &mir::Body<'tcx>,
    local: mir::Local,
    fuel: u32,
) -> Option<mir::Local> {
    if fuel == 0 {
        return None;
    }
    match unique_whole_local_def(mir_body, local)? {
        // `is_ok = Not(inner)` / a copy chain — hop through.
        mir::Rvalue::UnaryOp(mir::UnOp::Not, mir::Operand::Copy(p) | mir::Operand::Move(p))
        | mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
            if p.projection.is_empty() =>
        {
            null_check_addr_rec(mir_body, p.local, fuel - 1)
        }
        // `BitAnd(is_null, should_check)` — recurse into BOTH operands; only the
        // `is_null = Eq(addr, 0)` branch yields an address (the `should_check`
        // `Ne(SizeOf, 0)` branch has no address operand → `None`).
        mir::Rvalue::BinaryOp(mir::BinOp::BitAnd, box (a, b)) => {
            null_addr_from_operand(mir_body, a, fuel - 1)
                .or_else(|| null_addr_from_operand(mir_body, b, fuel - 1))
        }
        // `is_null = Eq(addr, 0)`: the address is the non-zero operand. NOTE: only
        // `Eq` (not `Ne`) — `Eq(_, 0)` is rustc's null predicate; a `Ne(SizeOf, 0)` is
        // the size guard, never the address.
        mir::Rvalue::BinaryOp(mir::BinOp::Eq, box (a, b)) => {
            match (is_zero_const(a), is_zero_const(b)) {
                (false, true) => operand_whole_local(a),
                (true, false) => operand_whole_local(b),
                _ => None,
            }
        }
        _ => None,
    }
}

fn null_addr_from_operand<'tcx>(
    mir_body: &mir::Body<'tcx>,
    op: &mir::Operand<'tcx>,
    fuel: u32,
) -> Option<mir::Local> {
    null_check_addr_rec(mir_body, operand_whole_local(op)?, fuel)
}

/// Whether `op` is the integer constant `0` (the null sentinel of a null check).
fn is_zero_const(op: &mir::Operand<'_>) -> bool {
    matches!(op, mir::Operand::Constant(box c)
        if c.const_.try_to_scalar_int().is_some_and(|s| s.is_null()))
}

/// Trust (goal item 2c — provably-safe pointer-assert discharge): ELIDE a
/// `MisalignedPointerDereference` / `NullPointerDereference` UB-check whose checked
/// address provably points into an INFALLIBLE box allocation of sufficient
/// alignment. rustc's `CheckAlignment`/null-check passes insert these before every
/// raw `*ptr`; the `vec!` box machinery (`Box::<[T; N]>::new_uninit()` → transmute →
/// `*const` → `usize` → `& (align-1)`) trips them on a pointer that is non-null and
/// `align_of::<[T; N]>()`-aligned BY CONSTRUCTION, so the check is statically dead.
/// Replacing the assert with a direct `Goto` to its success target removes a
/// provably-dead obligation — exactly the simplification rustc's own optimizer
/// performs under known alignment — and so can never hide real UB.
///
/// SOUNDNESS (0 false-PROVE is sacred): discharge is gated on
/// [`box_alloc_facts_for_addr`] (a narrow value-preserving trace to an infallible
/// box allocator) AND, for misalign, on `box_align >= required` where `required`
/// is the assert's OWN alignment constant. A re-cast to a higher-align pointee
/// (`*(box_u8 as *const u128)`) has `box_align < required` → KEPT → genuine
/// misalign still caught; a fallible `alloc::alloc` or arbitrary `usize as *T` never
/// matches the allocator gate → KEPT.
pub(crate) fn discharge_provably_safe_pointer_asserts<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    let typing_env = mir_body.typing_env(tcx);
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Assert { cond, msg, target, .. } = &bb_data.terminator().kind
        else {
            continue;
        };
        let discharge = match &**msg {
            mir::AssertKind::MisalignedPointerDereference { required, found } => {
                let Some(req) = (match required {
                    mir::Operand::Constant(box c) => {
                        c.const_.try_eval_target_usize(tcx, typing_env)
                    }
                    _ => None,
                }) else {
                    continue;
                };
                operand_whole_local(found)
                    .and_then(|addr| box_alloc_facts_for_addr(tcx, typing_env, mir_body, addr))
                    .is_some_and(|facts| facts.align.is_some_and(|a| a >= req))
            }
            mir::AssertKind::NullPointerDereference => null_check_addr_local(mir_body, cond)
                .and_then(|addr| box_alloc_facts_for_addr(tcx, typing_env, mir_body, addr))
                .is_some(),
            _ => continue,
        };
        if discharge {
            if let Some(block) = vbody.blocks.get_mut(bb.as_usize()) {
                block.terminator = Terminator::Goto(BlockId(target.as_usize()));
            }
        }
    }
}

/// Is `name` the `safe_def_path_str` of `std::io::Error`? `def_path_str` prints the
/// DEFINITIONAL path — `std::io::error::Error` (the type lives in the private
/// `std::io::error` module, re-exported as `std::io::Error`) — so accept either
/// rendering. Gated on a `std::`/`core::` origin + an `::io::` segment so a same-named
/// USER `io::Error` (with an arbitrary, possibly-panicking `Drop`) cannot match.
fn is_io_error_ty_name(name: &str) -> bool {
    (name.starts_with("std::") || name.starts_with("core::"))
        && name.contains("::io::")
        && name.ends_with("::Error")
}

/// The two `std::io::Error` constructors that yield an Os-variant error: a bare `i32`
/// OS error code that boxes NO user `dyn Error`. The resulting error's drop glue runs
/// no user destructor and is trivially total. `Error::new`/`::other`/`From`-conversions
/// build the CUSTOM variant (a boxed `dyn Error` whose `Drop` can panic) and are
/// deliberately excluded. Gated on a `std::`/`core::` + `::io::` origin so a same-named
/// user constructor cannot masquerade as the std one.
fn is_os_error_constructor(name: &str) -> bool {
    (name.starts_with("std::") || name.starts_with("core::"))
        && name.contains("::io::")
        && (name.ends_with("::last_os_error") || name.ends_with("::from_raw_os_error"))
}

/// Does the WHOLE local `local` have ANY `Assign` def (`_local = rvalue`, empty
/// projection) anywhere in the body? Distinguishes the TWO cases that
/// `unique_whole_local_def` collapses into the same `None` (convert.rs:2578): "zero
/// Assign defs" (this returns `false`) vs ">=2 Assign defs" (this returns `true`).
///
/// SOUNDNESS-CRITICAL: the provenance trace MUST NOT fall through to the Call-def check
/// when this is `true`. `unique_whole_local_def` returning `None` on >=2 Assign defs
/// skips the trace's rvalue/mixed-def guards, and `unique_call_def_for_local` (which
/// scans only `Call` terminators) is blind to those Assigns — so a local with >=2
/// whole-local move Assigns (>=1 rebinding to a Custom variant) PLUS one Os-constructor
/// Call def would be blessed as Os-provenance. That is a FALSE PROVE. Requiring this to
/// be `false` before trusting the unique Os Call means the Call is the local's SOLE
/// whole-local def, so its value provenance is fixed.
fn local_has_whole_local_assign_def(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    mir_body.basic_blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(&stmt.kind, mir::StatementKind::Assign(box (lhs, _))
                if lhs.local == local && lhs.projection.is_empty())
        })
    })
}

/// Does `drop_local` provably hold a value produced by an Os-variant `io::Error`
/// constructor? Traces backward through value-preserving WHOLE-LOCAL copy hops
/// (`_a = move/copy _b`) to the UNIQUE defining `Call`, which must be an Os constructor
/// (`is_os_error_constructor`). Mirrors the `alloc_call_box_facts` trace, minus the
/// pointer-cast hops (an io::Error is a moved struct value, never a re-cast pointer),
/// plus the &mut/RawPtr staleness gate.
///
/// FAIL-CLOSED (returns `false`) on ANY ambiguity or mutation risk — a wrong `true` is a
/// FALSE PROVE (a Custom-variant `dyn Error::drop` can panic):
///  * a local in `aliased_locals` (`&mut`/raw-pointer aliased): a `Deref`-store through
///    the alias could reassign it to a Custom variant with NO whole-local def the trace
///    can see (the SAME staleness gate `rewrite_range_contains_calls` uses);
///  * a mixed `Assign` + terminator def (`local_has_terminator_def`): another CFG path
///    may define the local via a Custom-variant `Call`;
///  * >=2 whole-local `Assign` defs: `unique_whole_local_def` returns `None` (colliding
///    with the "no Assign def" case), so BEFORE trusting the Call-def fallthrough we
///    require `!local_has_whole_local_assign_def` — otherwise a local with >=2 whole-
///    local move Assigns (>=1 binding a Custom variant) + one Os Call def would be
///    blessed via `unique_call_def_for_local` (blind to Assigns). This closes a
///    confirmed false PROVE;
///  * 0 or >=2 `Call` defs (`unique_call_def_for_local` returns `None` — ambiguous);
///  * any non-copy `Assign` rvalue (an `Error::new(..)`/`::other(..)` aggregate, a
///    `From`/`?` conversion result stored via `Assign`, a cast, or an unknown rvalue);
///  * a received (parameter) error with no in-body def.
fn error_local_has_os_provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    aliased_locals: &std::collections::HashSet<mir::Local>,
    drop_local: mir::Local,
) -> bool {
    let mut local = drop_local;
    for _ in 0..16 {
        // &mut/RawPtr staleness gate: a mutated value's provenance is NOT fixed by its
        // def, so refuse to bless it.
        if aliased_locals.contains(&local) {
            return false;
        }
        if let Some(def) = unique_whole_local_def(mir_body, local) {
            // A local defined by BOTH an `Assign` and a terminator is ambiguous.
            if local_has_terminator_def(mir_body, local) {
                return false;
            }
            match def {
                mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                    if p.projection.is_empty() =>
                {
                    local = p.local;
                    continue;
                }
                // Any other rvalue is NOT a value-preserving copy of an Os error.
                _ => return false,
            }
        }
        // `unique_whole_local_def` returned `None` — which is BOTH "zero Assign defs"
        // AND ">=2 Assign defs". Only the FORMER may consult the Call-def fallthrough:
        // in the ">=2" case the Call check (blind to Assigns) would bless a local that a
        // move-Assign rebinds to a Custom variant — a FALSE PROVE. Refuse unless there
        // is NO whole-local Assign def, i.e. the Call about to be checked is the local's
        // SOLE whole-local def.
        if local_has_whole_local_assign_def(mir_body, local) {
            return false;
        }
        // The local's only whole-local def must be a `Call` destination. Only an Os
        // constructor bottoms out the trace as Os-provenance. `unique_call_def_for_local`
        // returns `None` on 0 or >=2 Call defs, so this accepts only a single,
        // unambiguous Call def — the local's one and only whole-local write.
        if let Some(mir::TerminatorKind::Call { func, .. }) =
            unique_call_def_for_local(mir_body, local)
        {
            return is_os_error_constructor(&func_operand_name(tcx, func));
        }
        return false;
    }
    false
}

// ---------------------------------------------------------------------------------
// SPAWN-NAMESAFE (V2) — prove a `std::thread::Builder::spawn` / `::spawn_unchecked`
// call's thread name nul-free (or absent) and stamp the call with the
// `::<__trust_spawn_namesafe>` marker the bridge's absent-callee discharge honors.
//
// Designed against the REAL release-MIR shape (scratchpad spawn_mir.txt, trustc -O):
// `Builder::new` and `<&str as Into<String>>::into` are INLINED — the receiver's def
// is a surviving `Builder::name(move _3, move _4)` CALL, `_3` is the
// `Builder { name: Option::<String>::None, … }` AGGREGATE, `_4` is the
// `String { vec: _7 }` AGGREGATE whose buffer is a fresh `RawVecInner::
// try_allocate_in` allocation filled by exactly one `copy_nonoverlapping` from
// `_8 = const "…" as &[u8] (Transmute)` with `count == len == PtrMetadata(_8)` —
// and the terminal call is `Builder::spawn_unchecked::<{closure…}, ()>` (V1 traced
// the never-materialized source-level `Builder::spawn` chain and never fired; it
// also compared the BARE callee path while `func_operand_name` renders the concrete
// turbofish).
//
// SOUNDNESS SKELETON (a wrong PROVE here is the sacred violation):
//  * every traced local must have a UNIQUE, UNALIASED whole-local def (no multi/
//    mixed/projected defs, no direct `&mut`/RawPtr of its storage), AND
//  * every traced owned-value local is subject to MENTION-MULTISET ACCOUNTING: a
//    MIR visitor enumerates EVERY non-storage occurrence of the local in the body
//    and requires the multiset to equal exactly the recognized statements. This is
//    STRICTLY STRONGER than the `&mut`-borrow staleness gate alone, which is BLIND
//    at -O where an inlined `String::push('\0')` extracts the heap pointer by plain
//    FIELD-PROJECTION COPY (`copy ((((_7.0).0).0).0: NonNull<u8>)`) with no
//    `Ref`/`RawPtr` rvalue ever materializing. Any unaccounted read/write/call-arg/
//    drop/switch mention fails the match → the spawn stays UNMARKED (fail closed).
//  * heap-content claims additionally require: the ONE `CopyNonOverlapping` in the
//    whole body (its dst chained by address-preserving hops to the Vec's OWN buffer
//    pointer, its src to the nul-free promoted literal, its count to the literal's
//    `PtrMetadata`), NO `Deref`-store anywhere in the body, and a buffer that is a
//    FRESH `try_allocate_in` allocation (so no third party holds a pointer to it).
// ---------------------------------------------------------------------------------

/// SOUNDNESS-CRITICAL staleness gate, shared by `discharge_os_provenance_error_drops`
/// and the SPAWN-NAMESAFE trace: every local mutably borrowed (`Ref{mutable}`) or
/// address-taken (`RawPtr`, const OR mut — a `*const` can be cast to `*mut` and
/// written) ANYWHERE in the body. Such a local can be mutated in place via a
/// `Deref`-store its whole-local def can't see, so a def-based value claim is STALE.
fn mut_borrowed_or_address_taken_locals(
    mir_body: &mir::Body<'_>,
) -> std::collections::HashSet<mir::Local> {
    let mut set = std::collections::HashSet::new();
    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let mir::StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
                match rvalue {
                    mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                    | mir::Rvalue::RawPtr(_, place) => {
                        set.insert(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    set
}

/// Does any `Assign` statement or `Call` destination write a PROJECTED place based
/// at `local` (`(_l.f) = …`)? A projected write mutates the local without a
/// whole-local def, so every SPAWN-NAMESAFE unique-def claim must refuse it (the
/// inliner CAN collapse a by-value builder method into direct field stores).
fn local_has_projected_write(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    mir_body.basic_blocks.iter().any(|bb_data| {
        bb_data.statements.iter().any(|stmt| {
            matches!(&stmt.kind, mir::StatementKind::Assign(box (lhs, _))
                if lhs.local == local && !lhs.projection.is_empty())
        }) || matches!(&bb_data.terminator().kind, mir::TerminatorKind::Call { destination, .. }
            if destination.local == local && !destination.projection.is_empty())
    })
}

/// Like `unique_whole_local_def`, but also returns the def's `Location` (needed for
/// the mention-multiset accounting) — `None` for zero or multiple whole-local
/// `Assign` defs.
fn unique_whole_local_assign_with_loc<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    local: mir::Local,
) -> Option<(mir::Location, &'a mir::Rvalue<'tcx>)> {
    let mut found = None;
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        for (i, stmt) in bb_data.statements.iter().enumerate() {
            if let mir::StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind {
                if lhs.local == local && lhs.projection.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some((mir::Location { block: bb, statement_index: i }, rvalue));
                }
            }
        }
    }
    found
}

/// Like `unique_call_def_for_local`, but also returns the call's `Location` (the
/// terminator position, `statement_index == statements.len()`) for the
/// mention-multiset accounting.
fn unique_call_def_with_loc<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    local: mir::Local,
) -> Option<(mir::Location, &'a mir::TerminatorKind<'tcx>)> {
    let mut found = None;
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        if let mir::TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            if destination.local == local && destination.projection.is_empty() {
                if found.is_some() {
                    return None;
                }
                found = Some((
                    mir::Location { block: bb, statement_index: bb_data.statements.len() },
                    &bb_data.terminator().kind,
                ));
            }
        }
    }
    found
}

/// The UNIQUE whole-local def of `local` — either exactly one `Assign` and no call
/// dest, or exactly one call dest and no `Assign` — with its location. `None` (FAIL
/// CLOSED) on any other def shape: zero defs (a parameter), multiple defs, MIXED
/// `Assign`+`Call` defs, any PROJECTED write to the local, or a local whose storage
/// is `&mut`-borrowed / address-taken anywhere in the body (staleness).
enum SpawnUniqueDef<'a, 'tcx> {
    Assign(mir::Location, &'a mir::Rvalue<'tcx>),
    Call(mir::Location, &'a mir::TerminatorKind<'tcx>),
}

fn unique_unaliased_whole_def<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
    local: mir::Local,
    aliased: &std::collections::HashSet<mir::Local>,
) -> Option<SpawnUniqueDef<'a, 'tcx>> {
    if aliased.contains(&local) || local_has_projected_write(mir_body, local) {
        return None;
    }
    let has_assign = local_has_whole_local_assign_def(mir_body, local);
    let has_call = local_has_terminator_def(mir_body, local);
    match (has_assign, has_call) {
        (true, false) => unique_whole_local_assign_with_loc(mir_body, local)
            .map(|(loc, rv)| SpawnUniqueDef::Assign(loc, rv)),
        (false, true) => unique_call_def_with_loc(mir_body, local)
            .map(|(loc, kind)| SpawnUniqueDef::Call(loc, kind)),
        _ => None,
    }
}

/// Every non-storage MENTION of `local` in the body (each occurrence in any place
/// of any statement/terminator, with multiplicity, `StorageLive`/`StorageDead`/
/// debug-info excluded). Backbone of the SPAWN-NAMESAFE accounting: rustc's own MIR
/// visitor enumerates occurrences BY CONSTRUCTION, so no operand position (call
/// args, aggregate fields, assert conditions, drop places, index projections, …)
/// can be missed the way a hand-rolled match could.
fn local_mention_locations(mir_body: &mir::Body<'_>, local: mir::Local) -> Vec<mir::Location> {
    struct Collector {
        target: mir::Local,
        out: Vec<mir::Location>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Collector {
        fn visit_local(
            &mut self,
            local: mir::Local,
            context: mir::visit::PlaceContext,
            location: mir::Location,
        ) {
            if local == self.target && !matches!(context, mir::visit::PlaceContext::NonUse(_)) {
                self.out.push(location);
            }
        }
    }
    use mir::visit::Visitor as _;
    let mut collector = Collector { target: local, out: Vec::new() };
    collector.visit_body(mir_body);
    collector.out
}

/// `true` IFF the non-storage mentions of `local` are EXACTLY the `expected`
/// multiset of locations — the fail-closed accounting that guarantees no
/// unrecognized statement reads or writes the traced value (including reads that
/// merely LEAK its heap pointer to an unaccounted writer).
fn local_mentions_match(
    mir_body: &mir::Body<'_>,
    local: mir::Local,
    expected: &[mir::Location],
) -> bool {
    let sort = |mut v: Vec<mir::Location>| {
        v.sort_by_key(|l| (l.block.as_usize(), l.statement_index));
        v
    };
    sort(local_mention_locations(mir_body, local)) == sort(expected.to_vec())
}

/// Every mention of `local` must be one of the `allowed` (structurally vetted)
/// locations OR a benign POINTER-FREE read: `discriminant(local)` or a copy/move of
/// a place based at `local` whose type is a plain integer/bool/char, a
/// `core::num::niche_types` integer wrapper (the `UsizeNoHighBit` capacity read in
/// the inlined idiom's `assume` chain), or `TryReserveError` (the Err payload of
/// `try_allocate_in`, which carries no pointer into the fresh buffer). ANY other
/// mention — a call arg, a whole-value copy, a pointer-typed field read, a drop, a
/// write — fails (a leaked buffer pointer could be written through later).
fn mentions_are_recognized_or_pointer_free_reads<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    local: mir::Local,
    allowed: &[mir::Location],
) -> bool {
    for loc in local_mention_locations(mir_body, local) {
        if allowed.contains(&loc) {
            continue; // shape already vetted by the caller's structural match
        }
        let bb_data = &mir_body.basic_blocks[loc.block];
        let Some(stmt) = bb_data.statements.get(loc.statement_index) else {
            return false; // an unrecognized TERMINATOR use (call arg / drop / switch)
        };
        let mir::StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
            return false;
        };
        if lhs.local == local {
            return false; // any unrecognized WRITE
        }
        let benign = match rvalue {
            mir::Rvalue::Discriminant(place) => place.local == local,
            mir::Rvalue::Use(mir::Operand::Copy(place) | mir::Operand::Move(place), _) => {
                place.local == local
                    && ty_is_pointer_free_scalar(tcx, place.ty(&mir_body.local_decls, tcx).ty)
            }
            _ => false,
        };
        if !benign {
            return false;
        }
    }
    true
}

/// A type whose VALUE cannot carry (or reconstruct) a pointer into the traced
/// buffer: plain integers/bool/char, core's `niche_types` integer wrappers, and
/// `TryReserveError`. NOTE: a `usize` read is fine — deriving the buffer ADDRESS
/// would require reading the pointer FIELD, which is not in this set.
fn ty_is_pointer_free_scalar<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty.is_integral() || ty.is_bool() || ty.is_char() {
        return true;
    }
    match ty.ty_adt_def() {
        Some(adt) => {
            let path = crate::safe_def_path_str(tcx, adt.did());
            path.starts_with("core::num::niche_types::")
                || path.starts_with("std::num::niche_types::")
                || matches!(
                    path.as_str(),
                    "alloc::collections::TryReserveError" | "std::collections::TryReserveError"
                )
        }
        None => false,
    }
}

/// Is `local`'s OWN STORAGE directly aliased — a `Ref{mutable}`/`RawPtr` whose place
/// is based at `local` WITHOUT a leading `Deref`? (A Deref-first borrow like
/// `&raw const (*_lit)` targets the POINTEE — for a `&str` literal local that is the
/// IMMUTABLE promoted allocation, which cannot change which reference the local
/// holds nor, absent UB, its bytes.) Used ONLY for the literal `&str` local; every
/// OWNED value keeps the stronger whole-`aliased`-set gate.
fn local_storage_directly_aliased(mir_body: &mir::Body<'_>, local: mir::Local) -> bool {
    mir_body.basic_blocks.iter().any(|bb_data| {
        bb_data.statements.iter().any(|stmt| {
            let mir::StatementKind::Assign(box (_, rvalue)) = &stmt.kind else {
                return false;
            };
            let place = match rvalue {
                mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                | mir::Rvalue::RawPtr(_, place) => place,
                _ => return false,
            };
            place.local == local && !matches!(place.projection.first(), Some(mir::PlaceElem::Deref))
        })
    })
}

/// Does ANY statement or call destination store through a `Deref` projection? The
/// body-wide belt for the inlined-idiom lane: a fully-inlined interior mutation of
/// the String/Vec buffer bottoms out in a `*ptr = …` store, which this refuses
/// wholesale (fail closed — an unrelated raw store merely leaves the spawn
/// unmarked).
fn body_has_deref_store(mir_body: &mir::Body<'_>) -> bool {
    mir_body.basic_blocks.iter().any(|bb_data| {
        bb_data.statements.iter().any(|stmt| {
            matches!(&stmt.kind, mir::StatementKind::Assign(box (lhs, _))
                if lhs.projection.iter().any(|e| matches!(e, mir::PlaceElem::Deref)))
        }) || matches!(&bb_data.terminator().kind, mir::TerminatorKind::Call { destination, .. }
            if destination.projection.iter().any(|e| matches!(e, mir::PlaceElem::Deref)))
    })
}

/// Every `copy_nonoverlapping` intrinsic statement in the body, with location. The
/// inlined idiom requires EXACTLY ONE in the whole body — the literal-bytes fill.
fn copy_nonoverlapping_intrinsics<'a, 'tcx>(
    mir_body: &'a mir::Body<'tcx>,
) -> Vec<(mir::Location, &'a mir::CopyNonOverlapping<'tcx>)> {
    let mut out = Vec::new();
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        for (i, stmt) in bb_data.statements.iter().enumerate() {
            if let mir::StatementKind::Intrinsic(
                box mir::NonDivergingIntrinsic::CopyNonOverlapping(cno),
            ) = &stmt.kind
            {
                out.push((mir::Location { block: bb, statement_index: i }, cno));
            }
        }
    }
    out
}

/// The `FieldIdx` of the field NAMED `field` on `def_id`'s variant `variant_idx`.
/// SOUNDNESS: aggregate operands are resolved BY FIELD NAME from the AdtDef — never
/// by positional index — so a std field-order change can only make the recognizer
/// miss (fail closed), never read the WRONG field (e.g. blessing `stack_size:
/// None` as an absent NAME).
fn adt_field_idx<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    variant_idx: rustc_abi::VariantIdx,
    field: &str,
) -> Option<rustc_abi::FieldIdx> {
    let adt = tcx.adt_def(def_id);
    if variant_idx.as_usize() >= adt.variants().len() {
        return None;
    }
    adt.variant(variant_idx)
        .fields
        .iter_enumerated()
        .find_map(|(i, f)| (f.name.as_str() == field).then_some(i))
}

/// A rendered DIRECT `std::thread::Builder::spawn` / `::spawn_unchecked` callee —
/// bare, or with its concrete `::<F, T>` turbofish (`func_operand_name` renders the
/// monomorphized instantiation, e.g. `std::thread::Builder::spawn_unchecked::<
/// {closure@…}, ()>`; V1 compared the bare path for equality and therefore NEVER
/// fired). A crate-name collision on `std` renders with the `__trust_crate@…::`
/// disambiguation prefix (`direct_call_def_path`) and correctly fails this match.
fn is_builder_spawn_callee(name: &str) -> bool {
    const SPAWN: &str = "std::thread::Builder::spawn";
    const SPAWN_UNCHECKED: &str = "std::thread::Builder::spawn_unchecked";
    name == SPAWN
        || name == SPAWN_UNCHECKED
        || name.strip_prefix(SPAWN).is_some_and(|rest| rest.starts_with("::<"))
        || name.strip_prefix(SPAWN_UNCHECKED).is_some_and(|rest| rest.starts_with("::<"))
}

/// EXACTLY the trait-qualified renderings of the four byte-preserving std
/// `&str -> String` conversions (`.into()` / `String::from` / `.to_owned()` /
/// `.to_string()`), whole-string matched. Each clause pins the SELF type in
/// `<Self as Trait>` position — so a user path smuggling a std-trait PROJECTION
/// inside a generic arg (`mycrate::evil::<<str as std::borrow::ToOwned>::Owned>::
/// to_owned`) can never match — plus the std-origin trait and the method tail; the
/// orphan rule makes these std impls the ONLY `&str -> String` implementations of
/// those traits, and each is byte-preserving, so a nul-free source yields a
/// nul-free `String`. The CALLER additionally type-gates the destination
/// (`std String`) and the source (a compile-time nul-free `&str` literal).
fn is_std_str_to_string_callee(name: &str) -> bool {
    const STRING: [&str; 2] = ["std::string::String", "alloc::string::String"];
    const CONVERT: [&str; 2] = ["std::convert", "core::convert"];
    const TO_OWNED: [&str; 3] = [
        "<str as std::borrow::ToOwned>::to_owned",
        "<str as core::borrow::ToOwned>::to_owned",
        "<str as alloc::borrow::ToOwned>::to_owned",
    ];
    const TO_STRING: [&str; 2] = [
        "<str as std::string::ToString>::to_string",
        "<str as alloc::string::ToString>::to_string",
    ];
    for convert in CONVERT {
        for string in STRING {
            if name == format!("<&str as {convert}::Into<{string}>>::into")
                || name == format!("<{string} as {convert}::From<&str>>::from")
            {
                return true;
            }
        }
    }
    TO_OWNED.contains(&name) || TO_STRING.contains(&name)
}

/// `true` IFF `ty` is the std `String` ADT.
fn ty_is_std_string<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    matches!(ty.ty_adt_def(), Some(adt) if !adt.did().is_local()
        && matches!(crate::safe_def_path_str(tcx, adt.did()).as_str(),
            "alloc::string::String" | "std::string::String"))
}

/// SOUNDNESS-CRITICAL (SPAWN-NAMESAFE). `true` IFF `arg` resolves to a compile-time
/// `&str` constant whose bytes contain NO 0x00 — via a SPAWN-GRADE chain walk, NOT
/// the ungated `trace_operand_to_const`. That helper's `unique_whole_local_def`
/// counts ONLY `Assign`-statement defs and is BLIND to `Call`-destination defs, so a
/// `&str` local with one `_s = const "good"` Assign on one branch PLUS a
/// `_s = pick()` Call def on another (`let s = if c { "good" } else { pick() };`)
/// would be treated as uniquely const-defined while runtime can deliver `pick()`'s
/// NUL-containing result — a confirmed FALSE-PROVE shape in the non-inlined
/// conversion lane. Here every hop local must instead pass
/// `unique_unaliased_whole_def` with an `Assign` def ONLY (which refuses aliased
/// locals, projected writes, zero/multi defs, and mixed `Assign`+`Call` defs); hops
/// are whole-local `Use(copy/move)`; the root def must be `Use(Operand::Constant)`
/// passing `str_const_is_nul_free`. Extra shared READS of a hop local need no
/// mention accounting: `&str` is a shared reference to immutable bytes, and the
/// unaliased + unique-Assign-def gates already fix each hop's value at its def.
fn str_operand_is_nul_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    arg: &mir::Operand<'tcx>,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    if let mir::Operand::Constant(box c) = arg {
        return str_const_is_nul_free(tcx, c.const_);
    }
    let Some(mut local) = operand_whole_local(arg) else {
        return false;
    };
    for _ in 0..16 {
        let Some(SpawnUniqueDef::Assign(_, rv)) =
            unique_unaliased_whole_def(mir_body, local, aliased)
        else {
            return false;
        };
        match rv {
            mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                if p.projection.is_empty() =>
            {
                local = p.local;
            }
            mir::Rvalue::Use(mir::Operand::Constant(box c), _) => {
                return str_const_is_nul_free(tcx, c.const_);
            }
            _ => return false,
        }
    }
    false
}

/// `true` IFF `c` is a compile-time `&str` whose bytes contain NO interior 0x00.
/// The `&str` TYPE check comes FIRST because `try_get_slice_bytes_for_diagnostics`
/// `bug!`s on non-slice constants (same order as the `ConstValue::Str` lowering
/// above). UTF-8 permits interior NUL, so the byte scan is NOT redundant.
fn str_const_is_nul_free<'tcx>(tcx: TyCtxt<'tcx>, c: mir::Const<'tcx>) -> bool {
    let ty::TyKind::Ref(_, inner, _) = c.ty().kind() else {
        return false;
    };
    if !matches!(inner.kind(), ty::TyKind::Str) {
        return false;
    }
    if let mir::Const::Val(val, _) = c {
        if let Some(bytes) = val.try_get_slice_bytes_for_diagnostics(tcx) {
            return !bytes.contains(&0u8);
        }
    }
    false
}

/// A chain of value-preserving POINTER hops: `Use(copy/move)` of a whole local, or
/// an address-preserving `Cast` of a whole local whose source is pointer-like
/// (`cast_is_address_preserving` + `source_is_pointer_like`, the same hop algebra
/// as `box_alloc_facts_for_addr`). `hops` records every traversed local with its
/// unique def location (INCLUDING the root, last); `root_rvalue` is the first
/// non-hop def. `None` on any ambiguity (multi/mixed/zero defs, aliased hop local).
struct PtrChain<'a, 'tcx> {
    hops: Vec<(mir::Local, mir::Location)>,
    root_rvalue: &'a mir::Rvalue<'tcx>,
}

fn peel_ptr_chain<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &'a mir::Body<'tcx>,
    op: &mir::Operand<'tcx>,
    aliased: &std::collections::HashSet<mir::Local>,
) -> Option<PtrChain<'a, 'tcx>> {
    let mut local = operand_whole_local(op)?;
    let mut hops = Vec::new();
    for _ in 0..8 {
        if aliased.contains(&local) || local_has_terminator_def(mir_body, local) {
            return None;
        }
        let (loc, def) = unique_whole_local_assign_with_loc(mir_body, local)?;
        hops.push((local, loc));
        match def {
            mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _)
                if p.projection.is_empty() =>
            {
                local = p.local;
            }
            mir::Rvalue::Cast(
                kind,
                operand @ (mir::Operand::Copy(p) | mir::Operand::Move(p)),
                _,
            ) if cast_is_address_preserving(*kind)
                && p.projection.is_empty()
                && source_is_pointer_like(tcx, operand.ty(&mir_body.local_decls, tcx)) =>
            {
                local = p.local;
            }
            _ => return Some(PtrChain { hops, root_rvalue: def }),
        }
    }
    None
}

/// SOUNDNESS-CRITICAL (SPAWN-NAMESAFE, inlined lane). `true` IFF the `buf` operand
/// of the `Vec::<u8>` aggregate is a FRESH allocation — a `RawVec { inner: _i }`
/// aggregate whose `inner` is the Ok payload of the ONE
/// `alloc::raw_vec::RawVecInner::try_allocate_in` call — with mention accounting on
/// the whole chain so the buffer pointer provably never leaks to an unaccounted
/// writer BEFORE it enters the Vec. Freshness is what makes "the one
/// copy_nonoverlapping is the only write" a fact about the buffer's MEMORY, not
/// just about this body's syntax: nobody else holds a pointer to a fresh
/// allocation.
fn buf_operand_is_fresh_raw_vec<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    buf_op: &mir::Operand<'tcx>,
    vec_agg_loc: mir::Location,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    // `buf: move _rv` — the `RawVec { inner, _marker }` aggregate local.
    let Some(raw_vec_local) = operand_whole_local(buf_op) else {
        return false;
    };
    let Some(SpawnUniqueDef::Assign(raw_vec_loc, raw_vec_rv)) =
        unique_unaliased_whole_def(mir_body, raw_vec_local, aliased)
    else {
        return false;
    };
    if !local_mentions_match(mir_body, raw_vec_local, &[raw_vec_loc, vec_agg_loc]) {
        return false;
    }
    let mir::Rvalue::Aggregate(box mir::AggregateKind::Adt(did, vidx, _, _, _), ops) = raw_vec_rv
    else {
        return false;
    };
    if did.is_local()
        || !matches!(
            crate::safe_def_path_str(tcx, *did).as_str(),
            "alloc::raw_vec::RawVec" | "std::raw_vec::RawVec"
        )
    {
        return false;
    }
    let Some(inner_idx) = adt_field_idx(tcx, *did, *vidx, "inner") else {
        return false;
    };
    if ops.len() != tcx.adt_def(*did).variant(*vidx).fields.len() {
        return false;
    }
    // `inner: move _i`; `_i = move ((_r as Ok).0: RawVecInner)`.
    let Some(inner_local) = operand_whole_local(&ops[inner_idx]) else {
        return false;
    };
    let Some(SpawnUniqueDef::Assign(inner_loc, inner_rv)) =
        unique_unaliased_whole_def(mir_body, inner_local, aliased)
    else {
        return false;
    };
    // Extra mentions of the RawVecInner may only be pointer-free scalar reads (the
    // `UsizeNoHighBit` CAPACITY read in the inlined `assume` chain) — a read of the
    // pointer field would leak the buffer.
    if !mentions_are_recognized_or_pointer_free_reads(
        tcx,
        mir_body,
        inner_local,
        &[inner_loc, raw_vec_loc],
    ) {
        return false;
    }
    let mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _) = inner_rv else {
        return false;
    };
    if p.projection.len() != 2
        || !matches!(p.projection[0], mir::PlaceElem::Downcast(sym, v)
            if v.as_usize() == 0 && sym.is_none_or(|s| s.as_str() == "Ok"))
        || !matches!(p.projection[1], mir::PlaceElem::Field(f, _) if f.as_u32() == 0)
    {
        return false;
    }
    let result_local = p.local;
    // `_r = RawVecInner::try_allocate_in(…)` — the unique, FRESH allocation.
    let Some(SpawnUniqueDef::Call(call_loc, mir::TerminatorKind::Call { func, .. })) =
        unique_unaliased_whole_def(mir_body, result_local, aliased)
    else {
        return false;
    };
    let name = func_operand_name(tcx, func);
    let alloc_ok = [
        "alloc::raw_vec::RawVecInner::try_allocate_in",
        "std::raw_vec::RawVecInner::try_allocate_in",
    ]
    .iter()
    .any(|base| name == *base || name.strip_prefix(base).is_some_and(|r| r.starts_with("::<")));
    if !alloc_ok {
        return false;
    }
    // Result mentions: the defining call, the Ok read, plus only benign reads
    // (`discriminant(_r)`, the Err-payload `TryReserveError` extraction). A SECOND
    // Ok-payload read would leak the buffer pointer → fail.
    mentions_are_recognized_or_pointer_free_reads(
        tcx,
        mir_body,
        result_local,
        &[call_loc, inner_loc],
    )
}

/// SOUNDNESS-CRITICAL (SPAWN-NAMESAFE, release-MIR lane). `true` IFF the `Vec<u8>`
/// operand of a `String { vec: _v }` aggregate provably holds EXACTLY the bytes of
/// a compile-time nul-free `&str` literal (or, on the `PtrMetadata == 0` branch,
/// the empty prefix — also nul-free). Recognizes precisely the inlined
/// `str::to_owned` idiom of spawn_mir.txt:
///   `_v = Vec::<u8> { buf: <fresh try_allocate_in>, len: const 0 }`;
///   one `copy_nonoverlapping(dst = _v's own buffer ptr, src = &raw const (*_lit),
///   count = _n)`; one projected store `(_v.len) = copy _n`; `_n = PtrMetadata(_lit)`;
///   `_lit = const "…" as &[u8] (Transmute)` with nul-free bytes.
/// Every constituent is unique-def'd, unaliased, and mention-accounted; the body
/// has NO other `copy_nonoverlapping` and NO `Deref`-store at all. ANY deviation →
/// `false` (fail closed, the spawn stays UNMARKED).
fn inlined_string_vec_is_nul_free_literal<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    string_agg_loc: mir::Location,
    vec_operand: &mir::Operand<'tcx>,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    // NO copy-peel for the Vec local: the mention multiset below must see every use,
    // so the String aggregate's operand must BE the Vec local.
    let Some(vec_local) = operand_whole_local(vec_operand) else {
        return false;
    };
    if aliased.contains(&vec_local) || local_has_terminator_def(mir_body, vec_local) {
        return false;
    }
    // (1) UNIQUE whole-local def: `Vec::<u8> { buf, len: const 0 }` (fields resolved
    // BY NAME; `len` must start at zero so the final `len` is exactly the count).
    let Some((vec_def_loc, vec_rv)) = unique_whole_local_assign_with_loc(mir_body, vec_local)
    else {
        return false;
    };
    let mir::Rvalue::Aggregate(box mir::AggregateKind::Adt(vec_did, vec_vidx, _, _, _), vec_ops) =
        vec_rv
    else {
        return false;
    };
    if vec_did.is_local()
        || !matches!(
            crate::safe_def_path_str(tcx, *vec_did).as_str(),
            "alloc::vec::Vec" | "std::vec::Vec"
        )
    {
        return false;
    }
    let (Some(buf_idx), Some(len_idx)) = (
        adt_field_idx(tcx, *vec_did, *vec_vidx, "buf"),
        adt_field_idx(tcx, *vec_did, *vec_vidx, "len"),
    ) else {
        return false;
    };
    if vec_ops.len() != tcx.adt_def(*vec_did).variant(*vec_vidx).fields.len()
        || !is_zero_const(&vec_ops[len_idx])
    {
        return false;
    }
    // (2) The buffer is a FRESH `try_allocate_in` allocation (nobody else can hold a
    // pointer to it), with leak-free mention accounting on the whole buf chain.
    if !buf_operand_is_fresh_raw_vec(tcx, mir_body, &vec_ops[buf_idx], vec_def_loc, aliased) {
        return false;
    }
    // (3) EXACTLY one projected store to the Vec local: `(_v.len) = copy _n`.
    let mut len_store: Option<(mir::Location, mir::Local)> = None;
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        for (i, stmt) in bb_data.statements.iter().enumerate() {
            let mir::StatementKind::Assign(box (lhs, rv)) = &stmt.kind else {
                continue;
            };
            if lhs.local != vec_local || lhs.projection.is_empty() {
                continue;
            }
            if len_store.is_some()
                || lhs.projection.len() != 1
                || !matches!(lhs.projection[0], mir::PlaceElem::Field(f, _) if f == len_idx)
            {
                return false;
            }
            let mir::Rvalue::Use(mir::Operand::Copy(p) | mir::Operand::Move(p), _) = rv else {
                return false;
            };
            if !p.projection.is_empty() {
                return false;
            }
            len_store = Some((mir::Location { block: bb, statement_index: i }, p.local));
        }
    }
    let Some((len_loc, count_local)) = len_store else {
        return false;
    };
    // (4) The count/len local: unique def `PtrMetadata(copy _lit)` — the literal's
    // OWN length, so `len == count == |literal|` (a `usize` is immutable-by-copy;
    // extra reads of it are harmless and unconstrained).
    if aliased.contains(&count_local)
        || local_has_terminator_def(mir_body, count_local)
        || local_has_projected_write(mir_body, count_local)
    {
        return false;
    }
    let Some((_, count_rv)) = unique_whole_local_assign_with_loc(mir_body, count_local) else {
        return false;
    };
    let mir::Rvalue::UnaryOp(
        mir::UnOp::PtrMetadata,
        mir::Operand::Copy(lit_place) | mir::Operand::Move(lit_place),
    ) = count_rv
    else {
        return false;
    };
    if !lit_place.projection.is_empty() {
        return false;
    }
    let lit_local = lit_place.local;
    // (5) The literal local: unique def = `const "…" as &[u8] (Transmute)` of a
    // nul-free `&str` const. Its Deref-first `&raw const (*_lit)` borrow (the copy
    // source) targets the IMMUTABLE promoted allocation — writes through it are UB,
    // outside the semantic model (the same assumption rustc's own const-folding and
    // this file's const-based rewrites already make) — but its OWN storage must
    // never be directly aliased or multiply defined.
    if local_storage_directly_aliased(mir_body, lit_local)
        || local_has_terminator_def(mir_body, lit_local)
        || local_has_projected_write(mir_body, lit_local)
    {
        return false;
    }
    let Some((_, lit_rv)) = unique_whole_local_assign_with_loc(mir_body, lit_local) else {
        return false;
    };
    let mir::Rvalue::Cast(mir::CastKind::Transmute, mir::Operand::Constant(box lit_const), _) =
        lit_rv
    else {
        return false;
    };
    if !str_const_is_nul_free(tcx, lit_const.const_) {
        return false;
    }
    // (6) THE one `copy_nonoverlapping` in the WHOLE body: `count` is the literal's
    // length local; `dst` chains (address-preserving hops only) to a Field-projected
    // pointer read out of the Vec local ITSELF (`copy ((((_v.buf).0).0).0:
    // NonNull<u8>)`) — the buffer BASE, no arithmetic possible in the hop algebra;
    // `src` chains to `&raw const (*_lit)`.
    let intrinsics = copy_nonoverlapping_intrinsics(mir_body);
    let [(cno_loc, cno)] = intrinsics.as_slice() else {
        return false;
    };
    if operand_whole_local(&cno.count) != Some(count_local) {
        return false;
    }
    // Belt: both pointers must be BYTE pointers, so `count` counts BYTES and the
    // `len == count == |literal|` claim is in one unit. (An element-size mismatch
    // smuggled in by a transmute hop would over-read the promoted literal — UB,
    // outside the model — but the check keeps the recognizer self-contained.)
    let ptr_is_u8 = |op: &mir::Operand<'tcx>| {
        matches!(
            op.ty(&mir_body.local_decls, tcx).kind(),
            ty::TyKind::RawPtr(pointee, _)
                if matches!(pointee.kind(), ty::TyKind::Uint(ty::UintTy::U8))
        )
    };
    if !ptr_is_u8(&cno.dst) || !ptr_is_u8(&cno.src) {
        return false;
    }
    let Some(dst_chain) = peel_ptr_chain(tcx, mir_body, &cno.dst, aliased) else {
        return false;
    };
    let mir::Rvalue::Use(mir::Operand::Copy(dst_place) | mir::Operand::Move(dst_place), _) =
        dst_chain.root_rvalue
    else {
        return false;
    };
    if dst_place.local != vec_local
        || dst_place.projection.is_empty()
        || !dst_place.projection.iter().all(|e| matches!(e, mir::PlaceElem::Field(..)))
        || !source_is_pointer_like(tcx, dst_place.ty(&mir_body.local_decls, tcx).ty)
    {
        return false;
    }
    let Some(&(_, dst_root_loc)) = dst_chain.hops.last() else {
        return false;
    };
    let Some(src_chain) = peel_ptr_chain(tcx, mir_body, &cno.src, aliased) else {
        return false;
    };
    let mir::Rvalue::RawPtr(_, src_place) = src_chain.root_rvalue else {
        return false;
    };
    if src_place.local != lit_local
        || src_place.projection.len() != 1
        || !matches!(src_place.projection[0], mir::PlaceElem::Deref)
    {
        return false;
    }
    // (7) Mention-multiset accounting. The Vec local is touched by EXACTLY the four
    // recognized statements; each dst-chain pointer local by exactly its def and its
    // one consumer (so the buffer pointer NEVER escapes to an unaccounted user — the
    // gate the `&mut`-staleness set cannot provide at -O, where pointer extraction
    // is a plain field-projection copy). Src-side extra mentions would only re-read
    // the immutable literal and are already excluded by the chain's unique-def hops.
    if !local_mentions_match(
        mir_body,
        vec_local,
        &[vec_def_loc, len_loc, dst_root_loc, string_agg_loc],
    ) {
        return false;
    }
    let mut consumer_loc = *cno_loc;
    for &(hop_local, hop_loc) in &dst_chain.hops {
        if !local_mentions_match(mir_body, hop_local, &[hop_loc, consumer_loc]) {
            return false;
        }
        consumer_loc = hop_loc;
    }
    // (8) Body-wide belts: no `Deref`-store anywhere (a fully-inlined mutation
    // bottoms out in one), and — via (6) — no second copy intrinsic.
    if body_has_deref_store(mir_body) {
        return false;
    }
    // (9) The fill dominates the `len` store (same block, earlier index — the exact
    // emitted shape), so `len == count` is never published without the bytes.
    cno_loc.block == len_loc.block && cno_loc.statement_index < len_loc.statement_index
}

/// `true` IFF the `String` operand handed to the thread name (a `Builder::name`
/// argument or a `Some(_)` payload) provably contains no interior 0x00 — its local
/// is unique-def'd, unaliased, mentioned ONLY at its def and `use_loc`, and either
///   (a) the def is one of the four byte-preserving std `&str -> String` conversion
///       CALLS on a compile-time nul-free `&str` literal (non-inlined lane), or
///   (b) the def is the `String { vec }` AGGREGATE of the inlined `str::to_owned`
///       idiom (`inlined_string_vec_is_nul_free_literal`).
fn name_string_operand_is_nul_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    op: &mir::Operand<'tcx>,
    use_loc: mir::Location,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    let Some(string_local) = operand_whole_local(op) else {
        return false;
    };
    match unique_unaliased_whole_def(mir_body, string_local, aliased) {
        Some(SpawnUniqueDef::Call(
            def_loc,
            mir::TerminatorKind::Call { func, args, destination, .. },
        )) => {
            local_mentions_match(mir_body, string_local, &[def_loc, use_loc])
                && ty_is_std_string(tcx, destination.ty(&mir_body.local_decls, tcx).ty)
                && is_std_str_to_string_callee(&func_operand_name(tcx, func))
                && args
                    .first()
                    .is_some_and(|a| str_operand_is_nul_free(tcx, mir_body, &a.node, aliased))
        }
        Some(SpawnUniqueDef::Assign(def_loc, rv)) => {
            if !local_mentions_match(mir_body, string_local, &[def_loc, use_loc]) {
                return false;
            }
            let mir::Rvalue::Aggregate(box mir::AggregateKind::Adt(did, _, _, _, _), ops) = rv
            else {
                return false;
            };
            if did.is_local()
                || !matches!(
                    crate::safe_def_path_str(tcx, *did).as_str(),
                    "alloc::string::String" | "std::string::String"
                )
                || ops.len() != 1
            {
                return false;
            }
            inlined_string_vec_is_nul_free_literal(
                tcx,
                mir_body,
                def_loc,
                &ops[rustc_abi::FieldIdx::from_u32(0)],
                aliased,
            )
        }
        _ => false,
    }
}

/// Classify the `name` FIELD operand of an inlined `Builder { name, … }` aggregate:
///   (a) the `Option::<String>::None` AGGREGATE (variant `None`, zero operands — the
///       inlined `Builder::new()` of spawn_mir.txt) → namesafe;
///   (b) an `Option::<String>::Some(s)` AGGREGATE whose payload proves nul-free;
///   (c) ANYTHING else (a `const None` spelling, a moved-in parameter, a computed
///       Option) → `false`, fail closed.
fn option_string_operand_is_namesafe<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    op: &mir::Operand<'tcx>,
    use_loc: mir::Location,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    let Some(option_local) = operand_whole_local(op) else {
        return false;
    };
    let Some(SpawnUniqueDef::Assign(def_loc, rv)) =
        unique_unaliased_whole_def(mir_body, option_local, aliased)
    else {
        return false;
    };
    if !local_mentions_match(mir_body, option_local, &[def_loc, use_loc]) {
        return false;
    }
    let mir::Rvalue::Aggregate(box mir::AggregateKind::Adt(did, vidx, _, _, _), ops) = rv else {
        return false;
    };
    if did.is_local()
        || !matches!(
            crate::safe_def_path_str(tcx, *did).as_str(),
            "core::option::Option" | "std::option::Option"
        )
    {
        return false;
    }
    match tcx.adt_def(*did).variant(*vidx).name.as_str() {
        "None" => ops.is_empty(),
        "Some" if ops.len() == 1 => name_string_operand_is_nul_free(
            tcx,
            mir_body,
            &ops[rustc_abi::FieldIdx::from_u32(0)],
            def_loc,
            aliased,
        ),
        _ => false,
    }
}

/// SOUNDNESS-CRITICAL (SPAWN-NAMESAFE). `true` IFF the `Builder` receiver of a
/// spawn call provably carries a nul-free-or-absent thread name. The receiver must
/// be unique-def'd, unaliased, and mentioned ONLY at its def and the spawn itself;
/// its def is either
///   (a) a surviving `Builder::new()` CALL → `name: None`;
///   (b) a surviving `Builder::name(_, s)` CALL → validate `s` (the name REPLACES
///       whatever the incoming builder held, so arg 0 needs no inspection; `name`
///       takes `self` BY VALUE, and `stack_size`/`no_hooks` are name-independent);
///   (c) the inlined `Builder { name, stack_size, no_hooks }` AGGREGATE → classify
///       the `name` field (resolved BY NAME from the AdtDef, never by index).
/// EVERY other shape — an unknown builder method, a parameter, a multi-def or
/// aliased receiver — is `false` (fail closed).
fn spawn_receiver_is_namesafe<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    receiver: &mir::Operand<'tcx>,
    spawn_loc: mir::Location,
    aliased: &std::collections::HashSet<mir::Local>,
) -> bool {
    let Some(builder_local) = operand_whole_local(receiver) else {
        return false;
    };
    match unique_unaliased_whole_def(mir_body, builder_local, aliased) {
        Some(SpawnUniqueDef::Call(def_loc, mir::TerminatorKind::Call { func, args, .. })) => {
            if !local_mentions_match(mir_body, builder_local, &[def_loc, spawn_loc]) {
                return false;
            }
            let name = func_operand_name(tcx, func);
            if name == "std::thread::Builder::new" {
                return true; // `Builder { name: None, … }` by construction
            }
            if name == "std::thread::Builder::name" {
                // `Builder::name(self, name: String)` — the String is arg 1.
                return args.get(1).is_some_and(|a| {
                    name_string_operand_is_nul_free(tcx, mir_body, &a.node, def_loc, aliased)
                });
            }
            false
        }
        Some(SpawnUniqueDef::Assign(def_loc, rv)) => {
            if !local_mentions_match(mir_body, builder_local, &[def_loc, spawn_loc]) {
                return false;
            }
            let mir::Rvalue::Aggregate(box mir::AggregateKind::Adt(did, vidx, _, _, _), ops) = rv
            else {
                return false;
            };
            if did.is_local()
                || crate::safe_def_path_str(tcx, *did).as_str() != "std::thread::Builder"
            {
                return false;
            }
            let Some(name_idx) = adt_field_idx(tcx, *did, *vidx, "name") else {
                return false;
            };
            if ops.len() != tcx.adt_def(*did).variant(*vidx).fields.len() {
                return false;
            }
            option_string_operand_is_namesafe(tcx, mir_body, &ops[name_idx], def_loc, aliased)
        }
        // `None`, plus the type-level possibility of a `SpawnUniqueDef::Call` whose
        // payload is not a `Call` terminator (`unique_call_def_with_loc` never
        // constructs one, but the enum does not encode that): FAIL CLOSED.
        _ => false,
    }
}

/// SOUNDNESS-CRITICAL post-pass (SPAWN-NAMESAFE V2). Stamp `::<__trust_spawn_
/// namesafe>` onto every lowered `std::thread::Builder::spawn` / `::spawn_unchecked`
/// call whose thread name is PROVABLY nul-free or absent
/// (`spawn_receiver_is_namesafe`). The bridge's absent-callee discharge arm honors
/// the marker for THESE callees only, modeling the call panic-free — sound because
/// `Builder::spawn`'s ENTIRE body is `unsafe { self.spawn_unchecked(f) }`
/// (library/std/src/thread/builder.rs:185-192, no prelude — the two spellings share
/// ONE panic surface), and the only name-DEPENDENT panic in that surface is
/// `CString::new(name).expect("thread name may not contain interior null bytes")`
/// (`ThreadNameString: From<String>`, thread.rs, reached via `Thread::new`'s
/// `name.map(…)` only when a name was set) — exactly what the namesafe proof
/// discharges. A spawn we cannot prove namesafe is left UNMARKED and keeps its
/// fail-closed absent-callee panic obligation. Runs inside the Verification-purpose
/// post-pass block (the marker is a proof-oriented callee-name normalization, not
/// an executable lowering): needs both the rustc `mir::Body` (trace + accounting)
/// and the lowered `VerifiableBody` (whose call it stamps; block indices are
/// preserved by `convert_basic_block`'s enumeration order).
pub(crate) fn mark_spawn_namesafe_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    let aliased = mut_borrowed_or_address_taken_locals(mir_body);
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, args, .. } = &bb_data.terminator().kind else {
            continue;
        };
        let name = func_operand_name(tcx, func);
        if !is_builder_spawn_callee(&name) {
            continue;
        }
        // `spawn(self, f)` / `spawn_unchecked(self, f)` — the `Builder` is arg 0.
        let Some(receiver) = args.first() else {
            continue;
        };
        let spawn_loc = mir::Location { block: bb, statement_index: bb_data.statements.len() };
        if !spawn_receiver_is_namesafe(tcx, mir_body, &receiver.node, spawn_loc, &aliased) {
            continue; // fail closed — keep the absent-callee panic obligation
        }
        // Stamp the marker onto the LOWERED call. The exact-name re-check keeps the
        // stamp precise (and idempotent): if the lowered callee string is anything
        // else — opaqued, sentinel-rewritten, already marked — do nothing.
        let Some(block) = vbody.blocks.get_mut(bb.as_usize()) else {
            continue;
        };
        if let Terminator::Call { func: lowered, .. } = &mut block.terminator {
            if *lowered == name {
                *lowered = format!("{name}::<__trust_spawn_namesafe>");
            }
        }
    }
}

/// One compiler-authenticated paired-condvar wait site. This sidecar is never
/// serialized into [`VerifiableBody`]: a callee string inside public/extracted
/// MIR is not proof authority.
#[derive(Debug, Clone)]
pub struct CertifiedPairedCondvarWaitCallSite {
    session_seal: std::sync::Arc<()>,
    certificate_seal: std::sync::Arc<()>,
    stable_crate_id: u64,
    function_def_path: String,
    body_digest: String,
    block: trust_types::BlockId,
    callee: String,
    receiver_place: String,
    guard_place: String,
}

impl CertifiedPairedCondvarWaitCallSite {
    /// Whether this site was minted from this exact opaque crate certificate.
    /// Pointer identity, not the zero-sized seal's value equality, prevents a
    /// capability retained from another compiler Session (or an older
    /// certificate in the same Session) from being replayed against coincidentally
    /// identical function/body text.
    #[doc(hidden)]
    pub fn is_bound_to_certificate(
        &self,
        certificate: &crate::PairedCondvarCrateCertificate,
    ) -> bool {
        std::sync::Arc::ptr_eq(&self.session_seal, &certificate.session_seal)
            && std::sync::Arc::ptr_eq(&self.certificate_seal, &certificate.certificate_seal)
            && self.stable_crate_id == certificate.stable_crate_id
    }

    /// Exact extracted function identity authenticated by the collector.
    #[doc(hidden)]
    pub fn function_def_path(&self) -> &str {
        &self.function_def_path
    }

    /// Exact extracted MIR block authenticated by the collector.
    #[doc(hidden)]
    pub fn block(&self) -> trust_types::BlockId {
        self.block
    }

    /// Digest of the entire freshly extracted current body containing the site.
    #[doc(hidden)]
    pub fn body_digest(&self) -> &str {
        &self.body_digest
    }

    /// Exact TyCtxt-authenticated std wait callee spelling.
    #[doc(hidden)]
    pub fn callee(&self) -> &str {
        &self.callee
    }

    /// Exact post-transform rustc MIR receiver identity retained for audit.
    #[doc(hidden)]
    pub fn receiver_place(&self) -> &str {
        &self.receiver_place
    }

    /// Exact post-transform rustc MIR guard operand identity retained for audit.
    #[doc(hidden)]
    pub fn guard_place(&self) -> &str {
        &self.guard_place
    }
}

/// SOUNDNESS-CRITICAL post-pass (PAIRED-CONDVAR). Collect every lowered
/// `std::sync::Condvar::wait` call whose receiver is a shared borrow `&(*B).c`
/// of a field `c` carrying a whole-crate PAIRING
/// CERTIFICATE (`certify_paired_condvars_for_crate`, which privately invokes
/// `trust_vcgen::certify_paired_condvars` after owning the exhaustive TyCtxt
/// inventory). This collector binds each result to the owning function and
/// returns an opaque, constructor-free capability through the compiler-only
/// bridge feature. The bridge models only an exact function/block/callee match
/// as panic-free.
///
/// SOUND because the certificate proved, on the pre-steal whole-crate sweep:
/// every wait-family site on `(S, c)` is guard-provenance VALIDATED (the guard
/// is the SAME dynamic instance's `m` guard — an instance-pinned gen/kill
/// dataflow, kill-at-every-def), `c` is private, never escapes a whitelisted
/// consumer, and is freshly constructed in every constructor of `S`. The only
/// name-dependent panic in `Condvar::wait` is the pthread lane's two-mutex
/// `verify()` panic (`sys/sync/condvar/pthread.rs:39`, a compare_exchange of the
/// pal-mutex ADDRESS; poison maps to `Err`, `poison/condvar.rs:125-132`; the
/// futex/windows lanes have no verify) — exactly what pairing discharges.
/// Guard-pairing is a SEMANTIC invariant of every execution, but semantic
/// preservation alone is not authority. The no-caller-input sweep also records
/// an exact ledger entry for every genuine pre-transform wait. This collector
/// requires a unique ledger match (owner, block, DefId, rendered callee, source
/// span, receiver and guard identities, and originating inspected-body digest)
/// and then independently revalidates the current receiver shape. A transform,
/// including inlining, that changes or duplicates that identity simply loses
/// this optional discharge; it cannot mint a new site. The current callee is
/// resolved BY DefId to the NON-LOCAL
/// `std::sync::Condvar::wait` (never a name-string match — a local `mod
/// std::sync` impersonator has a local DefId and fails), receiver unique-def'd,
/// unaliased, mentioned only at its def and the wait, its borrow a
/// `Deref`/`Field`-only place whose base type is the certified LOCAL struct and
/// whose terminal field index+type re-verify against the certificate. Every
/// other shape — `wait_timeout`/`wait_while` (their tuple result / user
/// predicate stay fail-closed), a multi-def or aliased receiver, an uncertified
/// struct/field — is omitted and keeps its absent-callee panic obligation.
/// Runs in the Verification-purpose post-pass seam invoked by the verify
/// driver, which owns the crate certificate state. It deliberately does not
/// mutate `function.body`: suffix markers are source-forgeable and have no
/// authority.
pub fn collect_certified_paired_condvar_wait_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    certificate: &crate::PairedCondvarCrateCertificate,
) -> Vec<CertifiedPairedCondvarWaitCallSite> {
    // Never accept a caller-supplied public IR view. Freshly extract the entire
    // current rustc body and bind every capability to its exact digest.
    let function = crate::extract_function_with_contract_bundle(tcx, mir_body, None);
    let Some(body_digest) = crate::paired_condvar_body_digest(&function.body) else {
        return Vec::new();
    };
    // A token from another compiler Session confers nothing. The private
    // session/certificate Arc identities already bind this non-serializable
    // capability to the current immutable TyCtxt invocation; querying the
    // local crate_hash here is invalid during analysis (the hash is finalized
    // later) and is therefore neither needed nor safe as authority.
    let current_session_seal = crate::paired_condvar_session_seal(tcx);
    let owner = mir_body.source.def_id();
    let owner_key = crate::paired_def_key(tcx, owner);
    if !std::sync::Arc::ptr_eq(&certificate.session_seal, &current_session_seal)
        || certificate.stable_crate_id != tcx.stable_crate_id(LOCAL_CRATE).as_u64()
        || certificate.pairs.is_empty()
        || function.def_path != crate::safe_def_path_str(tcx, owner)
        || !certificate
            ._inspected_bodies
            .iter()
            .any(|inspected| inspected._owner == owner_key && inspected._promoted.is_none())
    {
        return Vec::new();
    }
    let mut sites = Vec::new();
    let aliased = mut_borrowed_or_address_taken_locals(mir_body);
    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Call { func, args, .. } = &bb_data.terminator().kind else {
            continue;
        };
        // Callee identity by DefId, never by rendered name: exactly the
        // non-local `std::sync::Condvar::wait` (NOT wait_timeout/wait_while).
        let mir::Operand::Constant(box const_op) = func else { continue };
        let rustc_middle::ty::TyKind::FnDef(callee_def_id, _) = const_op.const_.ty().kind() else {
            continue;
        };
        if callee_def_id.is_local()
            || crate::safe_def_path_str(tcx, *callee_def_id) != "std::sync::Condvar::wait"
            || !certificate._wait_callee_defs.contains(&crate::paired_def_key(tcx, *callee_def_id))
        {
            continue;
        }
        if args.len() != 2 {
            continue;
        }
        // Receiver: a unique-def'd, unaliased whole local mentioned ONLY at its
        // def and this wait, whose def is a SHARED borrow of a certified field.
        let Some(recv_local) = operand_whole_local(&args[0].node) else {
            continue;
        };
        let Some(SpawnUniqueDef::Assign(def_loc, rv)) =
            unique_unaliased_whole_def(mir_body, recv_local, &aliased)
        else {
            continue;
        };
        let wait_loc = mir::Location { block: bb, statement_index: bb_data.statements.len() };
        if !local_mentions_match(mir_body, recv_local, &[def_loc, wait_loc]) {
            continue;
        }
        let mir::Rvalue::Ref(_, mir::BorrowKind::Shared, place) = rv else {
            continue;
        };
        // `B ++ [Field(c)]` with a Deref/Field-only base chain.
        let Some((mir::PlaceElem::Field(fidx, _), prefix)) = place.projection.split_last() else {
            continue;
        };
        if !prefix.iter().all(|e| matches!(e, mir::PlaceElem::Deref | mir::PlaceElem::Field(..))) {
            continue;
        }
        // Every dereference in the receiver chain must be a Rust reference,
        // never a raw pointer. A shared `Rvalue::Ref` can borrow through
        // `*const S` inside unsafe code, but that is not the safe, instance-
        // pinned `&(*B).c` grammar certified by the crate analysis.
        if prefix.iter().enumerate().any(|(index, elem)| {
            matches!(elem, mir::PlaceElem::Deref)
                && !mir::Place::ty_from(place.local, &prefix[..index], &mir_body.local_decls, tcx)
                    .ty
                    .is_ref()
        }) {
            continue;
        }
        // Base struct: a LOCAL ADT carrying a certificate for THIS field index,
        // and the field type re-verifies as the genuine std Condvar.
        let base_ty = mir::Place::ty_from(place.local, prefix, &mir_body.local_decls, tcx).ty;
        let rustc_middle::ty::TyKind::Adt(adt_def, adt_args) = base_ty.kind() else {
            continue;
        };
        if !adt_def.did().is_local() || !adt_def.is_struct() {
            continue;
        }
        let Some(pairs) = certificate.pairs.get(&crate::paired_def_key(tcx, adt_def.did())) else {
            continue;
        };
        if !pairs.iter().any(|(c, mutex_field)| {
            if *c != fidx.as_usize() {
                return false;
            }
            let Some(field) = adt_def
                .non_enum_variant()
                .fields
                .get(rustc_abi::FieldIdx::from_usize(*mutex_field))
            else {
                return false;
            };
            let field_ty = field.ty(tcx, adt_args).skip_normalization();
            let rustc_middle::ty::TyKind::Adt(field_adt, _) = field_ty.kind() else {
                return false;
            };
            !field_adt.did().is_local()
                && crate::safe_def_path_str(tcx, field_adt.did()) == "std::sync::Mutex"
                && certificate
                    ._mutex_type_defs
                    .contains(&crate::paired_def_key(tcx, field_adt.did()))
        }) {
            continue;
        }
        let Some(field) = adt_def.non_enum_variant().fields.get(*fidx) else {
            continue;
        };
        // `skip_normalization` matches the candidate computation's field-type
        // vetting (`compute_sealed_backing_structs` idiom): S is a local
        // concrete struct, so its condvar field type needs no normalization.
        let field_ty = field.ty(tcx, adt_args).skip_normalization();
        let rustc_middle::ty::TyKind::Adt(field_adt, _) = field_ty.kind() else {
            continue;
        };
        if field_adt.did().is_local()
            || crate::safe_def_path_str(tcx, field_adt.did()) != "std::sync::Condvar"
            || !certificate
                ._condvar_type_defs
                .contains(&crate::paired_def_key(tcx, field_adt.did()))
        {
            continue;
        }
        // Bind the TyCtxt-authenticated call to the exact lowered block and
        // callee spelling. A stale/reordered or independently fabricated
        // VerifiableBody cannot acquire a sidecar entry.
        let name = func_operand_name(tcx, func);
        let Some(block) = function.body.blocks.get(bb.as_usize()) else {
            continue;
        };
        if block.id.0 != bb.as_usize() {
            continue;
        }
        let Terminator::Call { func: lowered, span, .. } = &block.terminator else {
            continue;
        };
        if *lowered != name {
            continue;
        }
        let receiver_place = format!("{:?}", args[0].node);
        let guard_place = format!("{:?}", args[1].node);
        let callee_key = crate::paired_def_key(tcx, *callee_def_id);
        let mut licenses = certificate._licensed_wait_sites.iter().filter(|license| {
            license.matches_current_identity(
                owner_key,
                None,
                bb.as_usize(),
                callee_key,
                &name,
                span,
                &receiver_place,
                &guard_place,
            ) && certificate._inspected_bodies.iter().any(|inspected| {
                inspected._owner == license._owner
                    && inspected._promoted == license._promoted
                    && inspected._mir_digest == license._inspected_mir_digest
            })
        });
        let Some(_license) = licenses.next() else {
            continue;
        };
        if licenses.next().is_some() {
            continue;
        }
        sites.push(CertifiedPairedCondvarWaitCallSite {
            session_seal: std::sync::Arc::clone(&certificate.session_seal),
            certificate_seal: std::sync::Arc::clone(&certificate.certificate_seal),
            stable_crate_id: certificate.stable_crate_id,
            function_def_path: function.def_path.clone(),
            body_digest: body_digest.clone(),
            block: block.id,
            callee: name,
            receiver_place,
            guard_place,
        });
    }
    sites
}

/// Discharge the drop-glue panic-freedom obligation for a `std::io::Error` value whose
/// VALUE-PROVENANCE is provably an Os-variant constructor (`io::Error::last_os_error` /
/// `io::Error::from_raw_os_error`). The Os variant stores a bare OS error code — it
/// boxes NO `dyn Error` — so its drop glue runs no user destructor and is trivially
/// total. When (and ONLY when) the specific dropped value provably originates from one
/// of those constructors, rewrite its `Drop` terminator to the plain `Goto` the bridge
/// already emits for any proven-total drop, discharging the obligation.
///
/// FAIL-CLOSED for EVERY other provenance — `io::Error::new`/`::other`, a `From`
/// conversion, a `?`-propagated or received (parameter) error, an ambiguous/multi-def
/// local, or a value reachable through a `&mut`/raw-pointer alias: the `Drop` terminator
/// is LEFT INTACT and the bridge keeps its `user Drop impls may panic` obligation.
/// Blessing a Custom-variant drop here would be a FALSE PROVE (its boxed
/// `dyn Error::drop` can panic). Mirrors `discharge_provably_safe_pointer_asserts`'
/// post-pass terminator rewrite; the value-preserving trace + `&mut`/RawPtr staleness
/// gate mirror `alloc_call_box_facts` / `rewrite_range_contains_calls`.
pub(crate) fn discharge_os_provenance_error_drops<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &mir::Body<'tcx>,
    vbody: &mut VerifiableBody,
) {
    let typing_env = mir_body.typing_env(tcx);

    // &mut/RawPtr staleness precompute (mirrors `rewrite_range_contains_calls`): every
    // local mutably borrowed (`Ref{mutable}`) or address-taken (`RawPtr`, const OR mut)
    // ANYWHERE in the body. Such a local can be mutated in place via a `Deref`-store the
    // whole-local-def trace cannot see, so its provenance is not fixed by its def.
    // Factored into `mut_borrowed_or_address_taken_locals` — the SAME predicate now also
    // backs the SPAWN-NAMESAFE trace, so the two gates can never drift.
    let aliased_locals = mut_borrowed_or_address_taken_locals(mir_body);

    for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Drop { place, target, .. } = &bb_data.terminator().kind else {
            continue;
        };
        // Only a WHOLE-LOCAL `std::io::Error` drop is a candidate. A projected drop
        // (`_x.field`) is not the value the constructor produced — fail-closed.
        if !place.projection.is_empty() {
            continue;
        }
        let drop_ty = place.ty(&mir_body.local_decls, tcx).ty;
        let drop_ty = tcx.normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(drop_ty));
        let ty::Adt(adt_def, _) = drop_ty.kind() else { continue };
        if !is_io_error_ty_name(&crate::safe_def_path_str(tcx, adt_def.did())) {
            continue;
        }
        if !error_local_has_os_provenance(tcx, mir_body, &aliased_locals, place.local) {
            continue;
        }
        // PROVEN Os-provenance: the drop glue is total. Replace the `Drop` with the plain
        // branch the bridge emits for any proven-total drop. Guard that the lowered
        // terminator is indeed the `Drop` (it always is for a rustc `Drop`) so an
        // unexpected shape is left untouched (fail-closed).
        if let Some(block) = vbody.blocks.get_mut(bb.as_usize()) {
            if matches!(block.terminator, Terminator::Drop { .. }) {
                block.terminator = Terminator::Goto(BlockId(target.as_usize()));
            }
        }
    }
}

fn convert_mir_const_value_to_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    ty: ty::Ty<'tcx>,
) -> Option<Operand> {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        TyKind::Bool => Some(Operand::Constant(ConstValue::Bool(value.try_to_bool()?))),
        TyKind::Char => Some(Operand::Constant(ConstValue::Uint(
            value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?,
            32,
        ))),
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
            Some(Operand::Constant(ConstValue::Int(val)))
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            Some(Operand::Constant(ConstValue::Uint(bits, width)))
        }
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let bits = value.try_to_bits_for_ty(tcx, ty::TypingEnv::fully_monomorphized(), ty)?;
            match width {
                32 | 64 => Some(Operand::Constant(ConstValue::FloatBits { bits, width })),
                16 | 128 => None,
                _ => unreachable!("rustc FloatTy widths are enumerated above"),
            }
        }
        _ if ty.is_unit() || is_fieldless_singleton_struct_ty(ty) => {
            Some(Operand::Constant(ConstValue::Unit))
        }
        _ => None,
    }
}

fn convert_ty_const_to_operand<'tcx>(tcx: TyCtxt<'tcx>, c: ty::Const<'tcx>) -> Option<Operand> {
    use rustc_middle::ty::TyKind;

    let value = c.try_to_value()?;
    let ty = value.ty;
    let typing_env = ty::TypingEnv::fully_monomorphized();

    match ty.kind() {
        TyKind::Bool => {
            return Some(Operand::Constant(ConstValue::Bool(value.try_to_bool()?)));
        }
        TyKind::Char => {
            let bits = value.try_to_bits(tcx, typing_env)?;
            return Some(Operand::Constant(ConstValue::Uint(bits, 32)));
        }
        TyKind::Int(int_ty) => {
            let width = crate::ty_convert::int_width_from_int_ty(int_ty, tcx);
            let bits = value.try_to_bits(tcx, typing_env)?;
            let val = rustc_abi::Size::from_bits(width as u64).sign_extend(bits) as i128;
            return Some(Operand::Constant(ConstValue::Int(val)));
        }
        TyKind::Uint(uint_ty) => {
            let width = crate::ty_convert::uint_width_from_uint_ty(uint_ty, tcx);
            let bits = value.try_to_bits(tcx, typing_env)?;
            return Some(Operand::Constant(ConstValue::Uint(bits, width)));
        }
        TyKind::Float(float_ty) => {
            let width: u32 = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            let bits = value.try_to_bits(tcx, typing_env)?;
            return match width {
                32 | 64 => Some(Operand::Constant(ConstValue::FloatBits { bits, width })),
                16 | 128 => None,
                _ => unreachable!("rustc FloatTy widths are enumerated above"),
            };
        }
        _ => {}
    }

    if ty.is_unit() || is_fieldless_singleton_struct_ty(ty) {
        Some(Operand::Constant(ConstValue::Unit))
    } else {
        None
    }
}

/// Convert a rustc Place to our Place.
fn convert_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: &mir::Place<'tcx>,
    typing_env: Option<ty::TypingEnv<'tcx>>,
) -> Place {
    let projections: Vec<Projection> = place
        .projection
        .iter()
        .map(|elem| match elem {
            mir::PlaceElem::Field(field, _) => Projection::Field(field.as_usize()),
            mir::PlaceElem::Index(local) => Projection::Index(local.as_usize()),
            mir::PlaceElem::Deref => Projection::Deref,
            mir::PlaceElem::Downcast(_, variant) => Projection::Downcast(variant.as_usize()),
            // Trust: M6 rung-7 sweep — `OpaqueCast`/`UnwrapUnsafeBinder` exist
            // specifically to reveal a place's type through an alias/opaque
            // position for a further projection, so this is the site MOST
            // likely (of the sites named in the rung-7 report's §2.1 residue)
            // to carry a `TyKind::Alias` node — thread `typing_env` the same
            // way as every other conversion in this module.
            mir::PlaceElem::OpaqueCast(ty) => {
                Projection::OpaqueCast(convert_ty_with_env(tcx, typing_env, ty))
            }
            mir::PlaceElem::UnwrapUnsafeBinder(ty) => {
                Projection::UnwrapUnsafeBinder(convert_ty_with_env(tcx, typing_env, ty))
            }
            mir::PlaceElem::ConstantIndex { offset, min_length, from_end } => {
                Projection::ConstantIndex {
                    offset: offset as usize,
                    min_length: min_length as usize,
                    from_end,
                }
            }
            mir::PlaceElem::Subslice { from, to, from_end } => {
                Projection::Subslice { from: from as usize, to: to as usize, from_end }
            }
        })
        .collect();

    Place { local: place.local.as_usize(), projections }
}

/// Convert an AssertKind to our AssertMessage.
fn convert_assert_message<'tcx>(
    msg: &mir::AssertKind<mir::Operand<'tcx>>,
) -> Result<AssertMessage, String> {
    match msg {
        mir::AssertKind::BoundsCheck { .. } => Ok(AssertMessage::BoundsCheck),
        mir::AssertKind::Overflow(bin_op, _, _) => match convert_supported_binop(*bin_op) {
            Some((our_op, _)) => Ok(AssertMessage::Overflow(our_op)),
            None => Err(format!(
                "AssertKind::Overflow uses unsupported BinOp::{bin_op:?}; preserving control flow as opaque"
            )),
        },
        mir::AssertKind::OverflowNeg(_) => Ok(AssertMessage::OverflowNeg),
        mir::AssertKind::DivisionByZero(_) => Ok(AssertMessage::DivisionByZero),
        mir::AssertKind::RemainderByZero(_) => Ok(AssertMessage::RemainderByZero),
        mir::AssertKind::ResumedAfterReturn(_) => Ok(AssertMessage::ResumedAfterReturn),
        mir::AssertKind::ResumedAfterPanic(_) => Ok(AssertMessage::ResumedAfterPanic),
        mir::AssertKind::MisalignedPointerDereference { .. } => {
            Ok(AssertMessage::MisalignedPointerDereference)
        }
        // Trust: #413 — map new rustc AssertKind variants to specific AssertMessage variants
        // instead of falling through to the wildcard Custom arm.
        mir::AssertKind::ResumedAfterDrop(_) => Ok(AssertMessage::ResumedAfterDrop),
        mir::AssertKind::NullPointerDereference => Ok(AssertMessage::NullPointerDereference),
        mir::AssertKind::InvalidEnumConstruction(_) => Ok(AssertMessage::InvalidEnumConstruction),
        // Trust: rust 1.99 added `NullReferenceConstructed` (forming a reference from a null
        // pointer is UB). trust-ir's `AssertMessage` has no dedicated variant, so surface it
        // soundly as a named `Custom` panic obligation rather than dropping the check.
        mir::AssertKind::NullReferenceConstructed => {
            Ok(AssertMessage::Custom("null reference constructed".to_string()))
        }
    }
}

/// Try to extract a function name from a Call operand.
/// The EXACT byte size of a bulk-allocation sink's element type `T`, via
/// `tcx.layout_of` on the call's monomorphized generic args (the element is the
/// first TYPE argument: `Vec::<T, A>::with_capacity` / `from_elem::<T>`). This is the
/// AUTHORITATIVE element size — recoverable for EVERY concrete element, including a
/// named struct/enum whose name does not spell its size (`struct Big([u8; 1<<35])`),
/// which the callee-turbofish spelling alone cannot size (SOUNDNESS, hunt-11: a
/// `Vec::<Big>::with_capacity(n < 2^28)` OOMs at runtime yet was reported safe). `None`
/// for a still-generic element (a generic fn the verifier checks polymorphically) or a
/// layout error — the caller then carries no size token and vcgen falls back to the
/// turbofish parse / count-only ceiling.
fn bulk_alloc_elem_byte_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic_args: ty::GenericArgsRef<'tcx>,
) -> Option<u64> {
    let elem_ty = generic_args.types().next()?;
    if elem_ty.has_non_region_param() {
        return None; // generic element — size is instantiation-dependent
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    tcx.layout_of(typing_env.as_query_input(elem_ty)).ok().map(|l| l.size.bytes())
}

/// The authoritative call-site name a `Terminator::Call` carries for `func` — the
/// `safe_def_path_str` of the callee, EXCEPT for the totality-rewrite classes
/// (`?`-total, bulk-alloc element-byte sink) which append a recognizable token.
///
/// `pub` so the verifier driver can key callee-contract summaries by the SAME name
/// the extracted call carries: keying by the bare `safe_def_path_str` left a
/// rewritten-name callee's `#[requires]` unfindable at the call site — a fail-open
/// (audit R2 #10). (The total-`Clone` / derived-trait sentinel override is applied
/// at the call-conversion site, not here, and only to contract-free calls.)
pub fn func_operand_name<'tcx>(tcx: TyCtxt<'tcx>, func: &mir::Operand<'tcx>) -> String {
    match func {
        mir::Operand::Constant(box const_op) => {
            let ty = const_op.const_.ty();
            match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, generic_args) => {
                    let diagnostic_path = crate::safe_def_path_str(tcx, *def_id);
                    // Contract-summary identity must include the exact call-site
                    // instantiation.  A bare DefId path aliases `f::<bool>` and
                    // `f::<i32>`, allowing the first summary inserted to type and
                    // discharge the second call.  Use rustc's canonical concrete
                    // path for every call; downstream `method_tail` deliberately
                    // strips trailing turbofish arguments for semantic classifiers.
                    let concrete_path =
                        crate::safe_def_path_str_with_args(tcx, *def_id, generic_args);
                    let generic = direct_call_def_path(tcx, *def_id, generic_args, concrete_path);
                    // W-BITINTRIN collision defense: diagnostic paths are
                    // source-spellable, so a user can otherwise declare
                    // `mod intrinsics { fn ctpop(..) }` and impersonate a body-less
                    // compiler intrinsic downstream. Stamp the non-source-spellable
                    // shared prefix only when TyCtxt confirms the direct FnDef is one
                    // of the exact modeled rustc intrinsics. Serialized-artifact
                    // authority remains the compiler transport/session; the string
                    // marker alone is intentionally not an authority token.
                    if let Some(marked) =
                        tcx_marked_pure_total_intrinsic_path(tcx, *def_id, &generic)
                    {
                        return marked;
                    }
                    // Trust (#84): the `?` operator desugars to a `Try::branch` call and
                    // (on the early-return arm) a `FromResidual::from_residual` call. For
                    // the std `Result`/`Option`/`ControlFlow` carriers — when no error
                    // `From` conversion runs — both are TOTAL (a pure discriminant split /
                    // identity re-wrap), but their bodies live in `core`/`std`, so the
                    // bridge's `resolve_call_target` would fail-close EVERY `?`-using
                    // function. Decide totality HERE, where the monomorphized signature
                    // (and the residual/target error types) is available — the bridge
                    // cannot, because the unit-error residual is extracted as an opaque
                    // constant that erases its type. Append a recognizable marker so the
                    // bridge models the result as a fresh unconstrained value. A CONVERTING
                    // `?` (whose `from_residual` runs a possibly-panicking user `From::from`)
                    // is NOT marked and stays fail-closed. See `trust_try_total_marker`.
                    if trust_try_total_marker(tcx, *def_id, generic_args) {
                        return format!("{generic}::<__trust_try_total>");
                    }
                    // For a bulk-allocation sink, re-render WITH concrete generic
                    // arguments so the element type (and `size_of::<T>()`) survives
                    // to trust-vcgen's capacity-overflow obligation. `def_path_str`
                    // alone renders the GENERIC definition (`Vec::<T>`), erasing the
                    // concrete element so a multi-byte `Vec::<[u8; N]>::with_capacity`
                    // was byte-size-blind (SOUNDNESS, hunt-11). Localized to sinks so
                    // no other callee string changes. The concrete `Vec::<…>` turbofish
                    // is a MIDDLE turbofish, so `method_tail`/`is_bulk_alloc_sink_call`
                    // (which `rsplit("::")`) still recover the same `with_capacity` tail.
                    let name = if is_bulk_alloc_sink_call(&diagnostic_path) {
                        let concrete = direct_call_def_path(
                            tcx,
                            *def_id,
                            generic_args,
                            crate::safe_def_path_str_with_args(tcx, *def_id, generic_args),
                        );
                        // Carry the AUTHORITATIVE element byte size (tcx.layout_of) as a
                        // trailing `::<__trust_elem_bytes_N>` token so vcgen sizes EVERY
                        // concrete element — including a named struct/enum whose spelling
                        // does not reveal its size. A trailing turbofish, so `method_tail`
                        // strips it and the `with_capacity` tail recognizers are unaffected.
                        match bulk_alloc_elem_byte_size(tcx, generic_args) {
                            Some(sz) => format!("{concrete}::<__trust_elem_bytes_{sz}>"),
                            None => concrete,
                        }
                    } else {
                        generic
                    };
                    // Apply the compiler-authenticated primitive-comparison
                    // sentinel rewrite HERE so the IR
                    // `Terminator::Call.func` string and the verifier's summary-registration
                    // key — BOTH `func_operand_name` — are computed by the SAME function and
                    // can never diverge for a sentineled callee. The other
                    // `func_operand_name` callers pass callees that do not meet
                    // the pinned primitive-comparison predicate.
                    // Sentinel FIRST: an authenticated core primitive comparison
                    // rewrites to `TRUST_TOTAL_CLONE_SENTINEL` and must keep that
                    // spelling. The
                    // devirtualization rename below must never pre-empt it — doing so
                    // would discard the authenticated total-call identity.
                    let sentineled = apply_total_clone_sentinel(tcx, func, name.clone());
                    if sentineled != name {
                        return sentineled;
                    }
                    // Devirtualization rename (see `devirtualized_callee_name`): a call
                    // that resolves to a LOCAL impl with available MIR takes the IMPL's
                    // name so the bridge matches its bundled, verified body. Fail-closed
                    // `None` keeps the trait spelling and falls through to the marker.
                    if let Some(devirt) = devirtualized_callee_name(tcx, *def_id, generic_args) {
                        return devirt;
                    }
                    // Trust (str char-boundary soundness): mark a `str` range-index
                    // callee so trust-vcgen can mint the extra UTF-8 char-boundary
                    // obligation. See `apply_str_index_marker`.
                    apply_str_index_marker(tcx, func, name)
                }
                _ => format!("{ty}"),
            }
        }
        _ => "<indirect>".to_string(),
    }
}

/// Mark the exact body-less compiler intrinsics modeled by trust-clean.
///
/// Returning `None` means the path must remain ordinary and untrusted. In
/// particular, textual suffixes never participate: only the compiler-owned
/// `IntrinsicDef` attached to this direct `FnDef` can mint the shared marker.
fn tcx_marked_pure_total_intrinsic_path(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    path: &str,
) -> Option<String> {
    let intrinsic = tcx.intrinsic(def_id)?;
    if !pure_total_intrinsic_marker_allowed(intrinsic.name.as_str(), intrinsic.must_be_overridden) {
        return None;
    }
    Some(format!("{}{}", trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX, path))
}

fn pure_total_intrinsic_marker_allowed(name: &str, must_be_overridden: bool) -> bool {
    must_be_overridden
        && matches!(
            name,
            "ctpop"
                | "cttz"
                | "ctlz"
                | "bswap"
                | "bitreverse"
                | "saturating_add"
                | "saturating_sub"
        )
}

/// Return the identity-bearing key used for a direct call and its modular
/// contract summary.
///
/// `TyCtxt::def_path_str` is diagnostic text, not an identity: two dependency
/// versions may have the same crate name and therefore render byte-for-byte
/// identical paths.  Leaving those paths bare lets one dependency's contract
/// summary overwrite or satisfy the other's call.  Preserve the familiar path
/// for local and globally unique crate names, but tag every external member of
/// an ambiguous name group with its stable crate id.  `@` cannot occur in a
/// Rust identifier, so the synthetic namespace cannot collide with a real def
/// path; retaining the original path as a suffix also preserves conservative
/// tail classifiers used by VC generation.
pub(crate) fn direct_call_def_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generic_args: ty::GenericArgsRef<'tcx>,
    path: String,
) -> String {
    let callee_crate_name = tcx.crate_name(def_id.krate);
    let local_has_same_name =
        !def_id.is_local() && tcx.crate_name(rustc_span::def_id::LOCAL_CRATE) == callee_crate_name;
    let another_external_has_same_name = !def_id.is_local()
        && tcx
            .crates(())
            .iter()
            .copied()
            .any(|krate| krate != def_id.krate && tcx.crate_name(krate) == callee_crate_name);
    let ambiguous_callee = local_has_same_name || another_external_has_same_name;
    let path = disambiguate_direct_call_path(
        path,
        def_id.is_local(),
        tcx.stable_crate_id(def_id.krate).as_u64(),
        ambiguous_callee,
    );

    // A concrete diagnostic path is still not an identity when one of its
    // generic arguments names either member of `shared_v1`/`shared_v2`: both
    // render `shared::T`. In the rare compilation containing any duplicate
    // crate-name group, bind every non-empty argument vector to rustc's stable
    // full-argument hash. Stable hashing lowers DefIds through
    // DefPathHash/StableCrateId, so nested type and const arguments retain the
    // dependency instance that display text erases. Ordinary crate graphs and
    // nongeneric calls remain byte-identical.
    let args_fingerprint = (!generic_args.is_empty() && has_duplicate_crate_names(tcx))
        .then(|| generic_args_fingerprint(tcx, generic_args));
    disambiguate_generic_call_path(path, args_fingerprint)
}

fn has_duplicate_crate_names(tcx: TyCtxt<'_>) -> bool {
    let mut seen = FxHashSet::default();
    if !seen.insert(tcx.crate_name(rustc_span::def_id::LOCAL_CRATE)) {
        return true;
    }
    tcx.crates(()).iter().copied().any(|krate| !seen.insert(tcx.crate_name(krate)))
}

fn generic_args_fingerprint<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic_args: ty::GenericArgsRef<'tcx>,
) -> Fingerprint {
    tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        hcx.while_hashing_spans(false, |hcx| {
            generic_args.stable_hash(hcx, &mut hasher);
        });
        hasher.finish()
    })
}

fn disambiguate_generic_call_path(path: String, args_fingerprint: Option<Fingerprint>) -> String {
    let Some(fingerprint) = args_fingerprint else { return path };
    let (lo, hi) = fingerprint.split();
    // Fixed-width halves are injective as text (`Fingerprint::to_hex` is not),
    // and `@` cannot occur in a real Rust identifier. The trailing balanced
    // turbofish is stripped by downstream method-tail classifiers.
    format!("{path}::<__trust_args@{lo:016x}{hi:016x}>")
}

fn disambiguate_direct_call_path(
    path: String,
    is_local: bool,
    stable_crate_id: u64,
    ambiguous_crate_name: bool,
) -> String {
    if is_local || !ambiguous_crate_name {
        path
    } else {
        format!("__trust_crate@{stable_crate_id:016x}::{path}")
    }
}

/// Remove every balanced trailing turbofish group while retaining the real
/// call path. Synthetic identity/semantic markers are deliberately stacked in
/// this position; semantic classifiers must inspect the underlying method,
/// never whichever marker happened to be appended last.
fn call_path_without_trailing_turbofish(mut path: &str) -> &str {
    while path.ends_with('>') {
        let mut depth = 0_i32;
        let mut open = None;
        for (index, byte) in path.as_bytes().iter().enumerate().rev() {
            match byte {
                b'>' => depth += 1,
                b'<' => {
                    depth -= 1;
                    if depth == 0 {
                        open = Some(index);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(index) = open else { break };
        path = path[..index].trim_end_matches(':');
    }
    path
}

/// DEVIRTUALIZED TRAIT CALL — the IMPL method a trait-method call actually
/// resolves to, when that impl is LOCAL and its MIR is available (i.e. exactly
/// what the callee-closure bundles). `None` otherwise, leaving the trait
/// spelling in place.
///
/// WHY: source like `ScrollbackAccess::line_count(sb)` — `sb` a CONCRETE
/// backend — leaves the TRAIT method's def_id in MIR with `Self` pinned in the
/// args. The closure resolves that, bundles the impl body, and registers it
/// under the IMPL path, while the call site rendered the TRAIT path. The bridge
/// matches callees BY NAME, so the bundled (and verified!) body was never found
/// and the call minted a fatal absent-callee row. Naming the resolved callee
/// makes the call MATCH its bundled body, so it is VERIFIED — not assumed.
///
/// FAIL-CLOSED GUARDS, each learned the hard way:
/// - `!has_non_region_param()` + `fully_monomorphized()`: this site has no
///   access to the CALLER's typing env, and feeding the CALLEE's param-env args
///   that still carry the caller's type/const params ICEs (`cannot find N/#0 in
///   param-env`). A polymorphic call is the unresolvable case anyway — it keeps
///   the trait spelling and stays fail-closed.
/// - std/foreign callees never resolve LOCAL, so every trait-path-keyed summary
///   is untouched.
///
/// Local derived impls deliberately take this same path. A source-spellable
/// `#[automatically_derived]` attribute has no proof authority, but its real MIR
/// is available and can be bundled and verified like any other local impl.
fn devirtualized_callee_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
    generic_args: ty::GenericArgsRef<'tcx>,
) -> Option<String> {
    if tcx.trait_of_assoc(def_id).is_none() || generic_args.has_non_region_param() {
        return None;
    }
    let instance =
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def_id, generic_args)
            .ok()
            .flatten()?;
    let resolved = instance.def_id();
    if resolved == def_id || !resolved.is_local() || !tcx.is_mir_available(resolved) {
        return None;
    }
    Some(crate::safe_def_path_str(tcx, resolved))
}

/// Rewrite a callee to `TRUST_TOTAL_CLONE_SENTINEL` when it is a PINNED-TOTAL std
/// primitive-comparison method (see [`is_pinned_total_std_primitive_cmp_call`]),
/// so the bridge models it as a total (havoc) call.
///
/// The old derived-totality lane is DEAD: a source/proc-macro-spellable
/// `#[automatically_derived]` attribute cannot authenticate rustc's builtin
/// expansion, so `is_automatically_derived` could not authorize an
/// obligation-free sentinel rewrite. The ONLY sentinel channel that survives is the
/// def-path-PINNED primitive-comparison table, whose authority is the resolved
/// callee's defining crate + a compiler-registered diagnostic trait + a builtin
/// primitive Self type — none of which is forgeable from source.
fn apply_total_clone_sentinel<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &mir::Operand<'tcx>,
    name: String,
) -> String {
    if let Some((method_def_id, gen_args)) = func.const_fn_def() {
        if is_pinned_total_std_primitive_cmp_call(tcx, method_def_id, gen_args) {
            return TRUST_TOTAL_CLONE_SENTINEL.to_string();
        }
    }
    name
}

/// P-PRIM-CMP — the pinned-total std primitive-comparison premise.
///
/// True iff this monomorphic call RESOLVES to one of the HAND-WRITTEN
/// `core::cmp::impls` primitive-comparison methods:
///   `<{iN,uN,bool,char} as PartialOrd>::{lt,le,gt,ge}`,
///   `<{iN,uN,bool,char} as Ord>::cmp`,
///   `<{iN,uN,bool,char} as PartialEq>::{eq,ne}`
/// for the 12 integer widths (`i8..i128`, `isize`, `u8..u128`, `usize`) + `bool`
/// + `char`. Each is a pure primitive comparison (`*self < *other`,
/// `three_way_compare`, `*self == *other`) with NO panic path — TOTAL BY
/// INSPECTION of the pinned std sources (library/core/src/cmp.rs `impls` module:
/// `partial_ord_methods_primitive_impl!`, `ord_impl!`, `partial_eq_impl!`, and
/// the explicit `impl {PartialOrd,Ord} for bool`).
///
/// AUTHENTICATION — why these def-paths are UNFORGEABLE (unlike the retired
/// `#[automatically_derived]`-keyed sentinel, a forgeable-attribute channel):
///  1. The call is RESOLVED to its concrete impl method (`Instance::try_resolve`
///     against `fully_monomorphized`). The bare trait-method `DefId`
///     `core::cmp::PartialOrd::lt` is SHARED by every impl and carries no
///     provenance; only the resolved impl method is authenticatable. A generic
///     (non-monomorphic) call fails closed BEFORE resolution.
///  2. The resolved method's DEFINING CRATE must be exactly `core`
///     (`crate_name(resolved.krate) == sym::core`) — a crate-of-`DefId` identity
///     check, NOT a def-path-string prefix a rename could spoof. Coherence (the
///     orphan rule) forbids any crate but `core` from implementing a std cmp
///     trait for a primitive, so a user `impl PartialOrd for UserType` — or a
///     `#[derive(PartialOrd)]` struct, whose generated methods live in the USER
///     crate — resolves OUTSIDE `core` and is rejected here.
///  3. The trait is matched by the compiler-REGISTERED diagnostic item
///     (`is_diagnostic_item(sym::{PartialOrd,Ord,PartialEq})`), which a user
///     crate cannot register (`#[rustc_diagnostic_item]` is std-only) — NOT by
///     the trait's name text (a user trait merely NAMED `PartialOrd` never
///     matches).
///  4. The Self type is read from the resolved impl's trait ref and must be a
///     builtin `ty::{Int,Uint,Bool,Char}` — a TYPE-SYSTEM fact, not a name.
///     Floats (`f16..f128`) are DELIBERATELY excluded (out of the pinned scope,
///     and their `NaN` partiality is not this table's concern); `clamp`/`min`/
///     `max`/`partial_cmp` are excluded by leaf name (`clamp` carries a
///     `min <= max` assert — a real panic path).
/// Every gate is compiler-authenticated; a same-shaped USER trait/type impl fails
/// gate (2) [resolves outside core], gate (3) [not the registered diagnostic
/// trait], or gate (4) [Self is an ADT, not a primitive]. Fail-closed throughout:
/// an unresolvable, non-core, non-diagnostic, wrong-leaf, or non-primitive-Self
/// call returns `false` and keeps its ordinary (obligation-bearing) callee.
fn is_pinned_total_std_primitive_cmp_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: rustc_span::def_id::DefId,
    gen_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    use rustc_hir::def::DefKind;
    use rustc_span::sym;

    // Fail closed on a non-monomorphic call: feeding caller params to the callee's
    // `fully_monomorphized` param-env ICEs (the `devirtualized_callee_name` /
    // `tcx_clone_is_total` precedent), and we cannot authenticate a concrete Self
    // type without a fully-substituted call.
    if gen_args.has_non_region_param() {
        return false;
    }

    // (1) Resolve to the concrete impl method — the only authenticatable identity.
    let Some(instance) = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        callee_def_id,
        gen_args,
    )
    .ok()
    .flatten() else {
        return false;
    };
    let resolved = instance.def_id();

    // (2) STRONG crate-of-DefId authentication: the resolved method is DEFINED in
    // `core` (the pinned std sources).
    if tcx.crate_name(resolved.krate) != sym::core {
        return false;
    }

    // Recover the resolved method's TRAIT impl. A primitive cmp method is always a
    // trait-impl item (`impls` module overrides lt/le/gt/ge, cmp, eq/ne for every
    // primitive); an inherent impl, or a bare default-method resolution with no
    // impl override, fails closed.
    let Some(impl_did) = tcx.impl_of_assoc(resolved) else {
        return false;
    };
    if !matches!(tcx.def_kind(impl_did), DefKind::Impl { of_trait: true }) {
        return false;
    }
    let trait_ref = tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization();
    let self_ty = trait_ref.self_ty();
    let trait_did = trait_ref.def_id;

    // (3) Trait identity by compiler-registered diagnostic item + pinned leaf.
    let method = tcx.item_name(resolved);
    let trait_method_ok = if tcx.is_diagnostic_item(sym::PartialOrd, trait_did) {
        matches!(method.as_str(), "lt" | "le" | "gt" | "ge")
    } else if tcx.is_diagnostic_item(sym::Ord, trait_did) {
        method.as_str() == "cmp"
    } else if tcx.is_diagnostic_item(sym::PartialEq, trait_did) {
        matches!(method.as_str(), "eq" | "ne")
    } else {
        false
    };
    if !trait_method_ok {
        return false;
    }

    // (4) Self is a builtin PRIMITIVE int/uint/bool/char (floats excluded).
    matches!(self_ty.kind(), ty::Int(_) | ty::Uint(_) | ty::Bool | ty::Char)
}

/// Trust (str char-boundary SOUNDNESS): a `str` range-index — `<str as
/// Index<RangeFrom<usize>>>::index(&s, a..)` and friends — renders through
/// `safe_def_path_str` as the GENERIC trait path `core::ops::index::Index::index`
/// (the concrete Self type is dropped), and `ty_convert` extracts `str` as
/// `[u8]`, so downstream trust-vcgen cannot tell a `&str` slice from a `&[u8]`
/// slice. That erasure is a FALSE-ACCEPT channel: a `str` range-slice panics not
/// only on the byte-bounds check (which vcgen models) but on the UTF-8
/// char-boundary check (which it does NOT — it is not a formula term), so a
/// byte-bounds proof over `&s[cut..]` at a computed `cut` (e.g. from a raw
/// `s.as_bytes()` scan) vacuously "proves" a program that panics mid-char at
/// runtime.
///
/// Preserve the Self identity across the erasure by appending a recognizable
/// trailing token — the SAME mechanism the hunt-11 bulk-alloc sink uses for the
/// element byte size. It is a trailing turbofish, so `method_tail` strips it and
/// every `::index` tail recognizer (`slice_method_panic` now routes through
/// `method_tail`) is unaffected; the token only reaches the RangeIndex body,
/// which mints the char-boundary obligation for str receivers alone.
///
/// Fires ONLY when Self is the primitive `str`. `String` range-slices already
/// fail closed (no modeled slice length), and `[u8]`/`[T]` slices carry no
/// char-boundary panic — both are left byte-identical, so drop-in Rust and the
/// entire slice corpus are untouched.
fn apply_str_index_marker<'tcx>(
    _tcx: TyCtxt<'tcx>,
    func: &mir::Operand<'tcx>,
    name: String,
) -> String {
    let semantic_path = call_path_without_trailing_turbofish(&name);
    if !semantic_path.ends_with("::index") && !semantic_path.ends_with("::index_mut") {
        return name;
    }
    // Trust (staircase shim, 1d1d11bed9 pattern): nested `if` instead of a
    // let-chain — this crate is edition 2021, where a 1.96-era genesis seed
    // rejects let-chains; semantics-preserving by definition.
    if let Some((_method, gen_args)) = func.const_fn_def() {
        if matches!(gen_args.types().next().map(|t| t.kind()), Some(ty::TyKind::Str)) {
            return format!("{name}::<__trust_str_index>");
        }
    }
    name
}

/// Trust (#84): is this monomorphized call a TOTAL (panic-free, no-user-code)
/// `?`-operator desugar call — `Try::branch` on a std carrier, or the identity
/// `FromResidual::from_residual`? Decided here (not in the bridge) because the
/// monomorphized signature carries the residual and target error types, which the
/// bridge loses (a unit-error residual extracts as an opaque, type-erased constant).
///
/// SOUNDNESS — anchored on the value TYPES of the monomorphized signature:
///  - `branch(self) -> ControlFlow<…>`: total iff `self` (input 0) is a std
///    `Result`/`Option`/`ControlFlow`. A nightly USER `Try` impl carries a user
///    receiver type and is NOT matched, so it stays fail-closed.
///  - `from_residual(residual) -> Self`: the std impl is
///    `impl<T, E, F: From<E>> FromResidual<Result<Infallible, E>> for Result<T, F>`
///    (and the `Option` analogue). It is total iff NO real `From` conversion runs:
///      * `Option` target — `from_residual` is `None => None`, never converts; OR
///      * `Result<T, F>` target whose error `F` EQUALS the residual error `E` — then
///        `F: From<E>` is the reflexive blanket `impl<T> From<T> for T` (coherence
///        forbids any other `From<T> for T`), which is the identity, total.
///    A CONVERTING `?` (`F: From<E>`, `E != F`) runs a user `From::from` that may
///    panic, so `E != F` is left UNMARKED → fail-closed (sound; conservatively
///    incomplete for the rare total non-identity `From`).
/// Public so the COMPILER can compute the same totality decision at
/// `collect_expected_absent_callees` time and carry it on the authenticated
/// set channel instead of a forgeable name suffix.
pub fn trust_try_total_marker<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
    generic_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    let path = crate::safe_def_path_str(tcx, def_id);
    let is_branch = path.ends_with("Try::branch");
    let is_from_residual = path.ends_with("FromResidual::from_residual");
    if !is_branch && !is_from_residual {
        return false;
    }
    // The monomorphized signature: input 0 and the output carry the concrete
    // carrier/residual types. `skip_binder` is safe — these methods bind no
    // late-bound regions in the input/output types we inspect. At MIR level the
    // types are already region-erased (`ReErased`), so the structural type
    // comparison below is region-insensitive without an explicit erase (and a
    // residual region mismatch would only fail-close — sound, never a false proof).
    let sig = tcx.fn_sig(def_id).instantiate(tcx, generic_args).skip_binder();
    let input0 = sig.inputs().first().copied();
    let Some(input0) = input0 else { return false };
    let output = sig.output();

    if is_branch {
        return std_try_carrier_kind(tcx, input0).is_some();
    }
    // from_residual: total iff the target is `Option`, or a `Result` whose error
    // type equals the residual's error type.
    match std_try_carrier_kind(tcx, output) {
        Some(StdCarrier::Option) => true,
        Some(StdCarrier::Result) => {
            match (result_err_ty(tcx, output), result_err_ty(tcx, input0)) {
                (Some(target_err), Some(residual_err)) => target_err == residual_err,
                _ => false,
            }
        }
        _ => false,
    }
}

#[derive(Clone, Copy)]
enum StdCarrier {
    Result,
    Option,
    ControlFlow,
}

/// Is `ty` a std `Result`/`Option`/`ControlFlow` ADT (the carriers whose `Try`
/// impls are compiler-total)? Anchored on the core/std/alloc def path so a USER
/// type named `Result`/`Option` in another crate is NOT matched.
fn std_try_carrier_kind<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<StdCarrier> {
    let ty::TyKind::Adt(def, _) = ty.kind() else { return None };
    let path = crate::safe_def_path_str(tcx, def.did());
    let std_path =
        path.starts_with("core::") || path.starts_with("std::") || path.starts_with("alloc::");
    if !std_path {
        return None;
    }
    match path.rsplit("::").next().unwrap_or(&path) {
        "Result" => Some(StdCarrier::Result),
        "Option" => Some(StdCarrier::Option),
        "ControlFlow" => Some(StdCarrier::ControlFlow),
        _ => None,
    }
}

/// The error type `E` of a std `Result<T, E>` (`E` is the second type argument).
fn result_err_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
    let ty::TyKind::Adt(_, args) = ty.kind() else { return None };
    if !matches!(std_try_carrier_kind(tcx, ty), Some(StdCarrier::Result)) {
        return None;
    }
    args.types().nth(1)
}

/// Trust: round-19 #3 — is this a direct call to a FOREIGN item (an
/// `extern { fn ... }` import)? Such items have no MIR body, so a call to one
/// crosses an unverified FFI boundary that the verifier must treat as FFI.
///
/// This is the authoritative signal `Terminator::Call.is_foreign` carries to
/// trust-vcgen, where name-substring detection (`ffi_vcgen::is_extern_call`)
/// under-approximates (it misses imports whose path lacks libc/extern/ffi).
/// We deliberately key on `is_foreign_item`, NOT the ABI: an in-tree
/// `extern "C" fn` DEFINITION has MIR and is verified like any other function,
/// so it is not the over-claim hole; the body-less import is. Indirect calls
/// and non-`FnDef` operands are not foreign here.
fn func_operand_is_foreign<'tcx>(tcx: TyCtxt<'tcx>, func: &mir::Operand<'tcx>) -> bool {
    match func {
        mir::Operand::Constant(box const_op) => match const_op.const_.ty().kind() {
            rustc_middle::ty::TyKind::FnDef(def_id, _) => tcx.is_foreign_item(*def_id),
            _ => false,
        },
        _ => false,
    }
}

/// Trust: T5A — is the callee's fn SIGNATURE unsafe? Mirrors rustc's
/// call-unsafety rule EXACTLY (check_unsafety.rs, and the compiler-side
/// `synthetic_unmodeled_unsafe_call_vcs` in trust_verify.rs): unsafe iff the
/// instantiated signature's safety is `Unsafe` AND the callee is not a
/// `safe_target_features` fn. The `safe_target_features` gate is essential: a
/// target_feature_11 fn has an unsafe SIGNATURE but is safe to call from a
/// same-feature context, so keying purely on the signature would FALSELY
/// demand a SAFETY comment for such in-context calls.
///
/// This is the authoritative signal `Terminator::Call.is_unsafe_sig` carries
/// to trust-vcgen's unsafe-block detection; the `is_unsafe_fn_call` name list
/// stays only as a fallback for synthetic MIR that predates the field.
/// Non-`FnDef` operands (fn pointers / indirect calls) return false —
/// conservative-for-lint: the consumer demand is the documentation-only
/// missing-SAFETY lint, so a false here can only DROP a doc demand, never
/// create a false proof (indirect calls stay opaque / fail-closed upstream).
fn func_operand_is_unsafe_sig<'tcx>(tcx: TyCtxt<'tcx>, func: &mir::Operand<'tcx>) -> bool {
    match func {
        mir::Operand::Constant(box const_op) => match const_op.const_.ty().kind() {
            rustc_middle::ty::TyKind::FnDef(def_id, args) => {
                let unsafe_sig = matches!(
                    tcx.fn_sig(*def_id).instantiate(tcx, args).skip_binder().safety(),
                    rustc_hir::Safety::Unsafe
                );
                unsafe_sig && !tcx.codegen_fn_attrs(*def_id).safe_target_features
            }
            _ => false,
        },
        _ => false,
    }
}

/// Convert a rustc Span to our SourceSpan.
pub(crate) fn convert_span(tcx: TyCtxt<'_>, span: Span) -> SourceSpan {
    if span.is_dummy() {
        return SourceSpan::default();
    }

    let source_map = tcx.sess.source_map();
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());

    SourceSpan {
        file: lo.file.name.prefer_local_unconditionally().to_string(),
        line_start: lo.line as u32,
        col_start: lo.col.0 as u32,
        line_end: hi.line as u32,
        col_end: hi.col.0 as u32,
    }
}

// Tests for atomic intrinsic detection.
// These tests exercise parse_atomic_intrinsic with synthetic function names
// and do not require a rustc TyCtxt.
#[cfg(test)]
mod tests {
    fn mock_paired_condvar_certificate(
        session_seal: std::sync::Arc<()>,
        certificate_seal: std::sync::Arc<()>,
        stable_crate_id: u64,
    ) -> crate::PairedCondvarCrateCertificate {
        crate::PairedCondvarCrateCertificate {
            session_seal,
            certificate_seal,
            stable_crate_id,
            pairs: Default::default(),
            _condvar_type_defs: Default::default(),
            _mutex_type_defs: Default::default(),
            _wait_callee_defs: Default::default(),
            _inspected_bodies: Vec::new(),
            _licensed_wait_sites: Default::default(),
        }
    }

    #[test]
    fn paired_condvar_site_rejects_cross_session_and_stale_certificate_replay() {
        let session_a = std::sync::Arc::new(());
        let certificate_a_seal = std::sync::Arc::new(());
        let certificate_a = mock_paired_condvar_certificate(
            std::sync::Arc::clone(&session_a),
            std::sync::Arc::clone(&certificate_a_seal),
            17,
        );
        let site = super::CertifiedPairedCondvarWaitCallSite {
            session_seal: std::sync::Arc::clone(&session_a),
            certificate_seal: std::sync::Arc::clone(&certificate_a_seal),
            stable_crate_id: 17,
            function_def_path: "crate::wait".into(),
            body_digest: "body-digest".into(),
            block: trust_types::BlockId(3),
            callee: "std::sync::Condvar::wait".into(),
            receiver_place: "move _4".into(),
            guard_place: "move _5".into(),
        };

        assert!(site.is_bound_to_certificate(&certificate_a));
        assert!(site.clone().is_bound_to_certificate(&certificate_a));

        let another_session_same_revision =
            mock_paired_condvar_certificate(std::sync::Arc::new(()), std::sync::Arc::new(()), 17);
        assert!(!site.is_bound_to_certificate(&another_session_same_revision));

        let newer_certificate_same_session = mock_paired_condvar_certificate(
            std::sync::Arc::clone(&session_a),
            std::sync::Arc::new(()),
            17,
        );
        assert!(!site.is_bound_to_certificate(&newer_certificate_same_session));

        let wrong_revision = mock_paired_condvar_certificate(
            std::sync::Arc::clone(&session_a),
            std::sync::Arc::clone(&certificate_a_seal),
            18,
        );
        assert!(!site.is_bound_to_certificate(&wrong_revision));
    }

    #[test]
    fn bit_intrinsic_marker_requires_backend_override_and_exact_name() {
        use super::pure_total_intrinsic_marker_allowed as allowed;

        for name in
            ["ctpop", "cttz", "ctlz", "bswap", "bitreverse", "saturating_add", "saturating_sub"]
        {
            assert!(allowed(name, true), "body-less modeled intrinsic must be marked: {name}");
            assert!(
                !allowed(name, false),
                "a #[rustc_intrinsic] function with a body is not backend intrinsic authority: {name}"
            );
        }
        for name in [
            "cttz_nonzero",
            "ctlz_nonzero",
            "unchecked_add",
            "unchecked_mul",
            "saturating_mul",
            "transmute",
            "write_bytes",
            "",
        ] {
            assert!(!allowed(name, true), "unmodeled intrinsic must remain unmarked: {name}");
        }
    }

    #[test]
    fn is_panic_diverging_call_matches_assert_panic_family() {
        use super::is_panic_diverging_call as p;
        // Recognized panic sites (lockstep with trust-ir-bridge is_panic_call):
        // a diverging call to any of these routes to the bridge's panic-freedom
        // shape instead of an unlowerable Opaque terminator.
        assert!(p("core::panicking::panic"));
        assert!(p("core::panicking::panic_fmt"));
        assert!(p("std::rt::begin_panic"));
        assert!(p("core::panicking::panic_bounds_check"));
        assert!(p("core::panicking::panic_nounwind"));
        assert!(p("core::panicking::panic_cannot_unwind"));
        assert!(p("foo::bar::panic"));
        // Non-panic diverging callees must STAY opaque / fail-closed.
        assert!(!p("std::process::exit"));
        assert!(!p("my_crate::run_forever"));
        assert!(!p("core::mem::drop"));
    }

    #[test]
    fn string_only_noreturn_paths_never_create_totality() {
        assert!(!super::is_total_noreturn_call("std::process::exit"));
        assert!(!super::is_total_noreturn_call("my::process::exit"));
    }

    #[test]
    fn is_bulk_alloc_sink_call_matches_recognizer_tails() {
        use super::is_bulk_alloc_sink_call as s;
        // Mirrors trust-vcgen's bulk_alloc_call + is_collect_sink: a DIRECT call
        // to one of these whose post-inlining shape has no normal-return target
        // is routed to a real `Call` (not opaque) so the size arg reaches the
        // UnboundedAllocation recognizer.
        assert!(s("std::vec::Vec::<u8>::with_capacity"));
        assert!(s("alloc::vec::Vec::<u64>::with_capacity_in"));
        assert!(s("std::vec::Vec::<u8>::reserve"));
        assert!(s("std::vec::Vec::<u8>::reserve_exact"));
        assert!(s("alloc::vec::Vec::<u8>::resize"));
        assert!(s("alloc::vec::Vec::<u8>::resize_with"));
        assert!(s("alloc::vec::from_elem"));
        assert!(s("core::iter::Iterator::collect"));
        assert!(s("core::iter::FromIterator::from_iter"));
        // Non-sink calls must NOT be re-routed (stay opaque / fail-closed).
        assert!(!s("my_crate::helper::compute"));
        assert!(!s("core::mem::drop"));
        assert!(!s("std::process::exit"));
    }

    #[test]
    fn duplicate_crate_call_paths_are_injective_and_keep_the_real_suffix() {
        let path = "shared::contracted".to_string();
        assert_eq!(
            disambiguate_direct_call_path(path.clone(), true, 0x11, true),
            path,
            "local calls keep their call-graph identity"
        );
        assert_eq!(
            disambiguate_direct_call_path(path.clone(), false, 0x11, false),
            path,
            "unique external crates keep the stable diagnostic spelling"
        );

        let first = disambiguate_direct_call_path(path.clone(), false, 0x11, true);
        let second = disambiguate_direct_call_path(path.clone(), false, 0x22, true);
        assert_eq!(first, "__trust_crate@0000000000000011::shared::contracted");
        assert_eq!(second, "__trust_crate@0000000000000022::shared::contracted");
        assert_ne!(first, second, "dependency versions must not share contract-summary keys");
        assert!(first.ends_with(&path));
        assert!(second.ends_with(&path));
        assert!(
            first.contains('@'),
            "the reserved marker must be impossible to forge as a Rust def path"
        );
    }

    #[test]
    fn duplicate_crate_generic_arguments_get_fixed_width_stable_identity() {
        let path = "local::contracted::<shared::T>".to_string();
        assert_eq!(
            disambiguate_generic_call_path(path.clone(), None),
            path,
            "ordinary crate graphs must keep existing call keys byte-identical"
        );

        // These pairs would collide if their unpadded hexadecimal halves were
        // concatenated (`1` + `23` versus `12` + `3`). Fixed-width rendering
        // retains the full 128-bit stable fingerprint.
        let first =
            disambiguate_generic_call_path(path.clone(), Some(Fingerprint::new(0x1_u64, 0x23_u64)));
        let second =
            disambiguate_generic_call_path(path.clone(), Some(Fingerprint::new(0x12_u64, 0x3_u64)));
        assert_eq!(first, format!("{path}::<__trust_args@00000000000000010000000000000023>"));
        assert_eq!(second, format!("{path}::<__trust_args@00000000000000120000000000000003>"));
        assert_ne!(first, second, "distinct dependency identities must not share summary keys");
        assert!(
            first.starts_with(&path),
            "the real call path must remain available to classifiers"
        );
        assert!(first.contains('@'), "the identity namespace must be impossible to forge in Rust");
    }

    #[test]
    fn semantic_method_identity_survives_stacked_generic_markers() {
        let index = "core::ops::index::Index::index::<__trust_args@001122>";
        assert_eq!(
            call_path_without_trailing_turbofish(index),
            "core::ops::index::Index::index",
            "the generic-identity marker must not hide the str-index classifier"
        );
        let stacked = "core::ops::index::Index::index::<__trust_args@001122>::<__trust_str_index>";
        assert_eq!(
            call_path_without_trailing_turbofish(stacked),
            "core::ops::index::Index::index",
            "all stacked markers must expose the same real method"
        );
        assert!(
            call_path_without_trailing_turbofish(
                "core::clone::Clone::clone::<__trust_args@001122>"
            )
            .ends_with("::Clone::clone"),
            "generic identity must not disable the total-Clone classifier"
        );
    }

    #[test]
    fn is_alloc_failure_abort_call_matches_std_handler_symbols_only() {
        use super::is_alloc_failure_abort_call as a;
        // The std allocation-failure handler symbols: diverging ABORT (not panic),
        // routed to a path-ending `Return` so the enclosing fn lowers instead of
        // wedging at the opaque bail.
        assert!(a("alloc::alloc::handle_alloc_error"));
        assert!(a("std::alloc::handle_alloc_error"));
        assert!(a("alloc::alloc::__rust_alloc_error_handler"));
        assert!(a("alloc::alloc::__rdl_oom"));
        // STD-ORIGIN GATE: a like-named user fn must NOT enter the class.
        assert!(!a("my_crate::alloc::handle_alloc_error"));
        // A genuine panic path must NOT be absorbed here (it stays a real obligation).
        assert!(!a("alloc::raw_vec::capacity_overflow"));
        assert!(!a("core::panicking::panic"));
        assert!(!a("std::process::exit"));
    }

    use super::*;
    extern crate rustc_driver;
    extern crate rustc_hir;
    extern crate rustc_interface;

    use std::collections::BTreeMap;
    use std::io;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, OnceLock};

    use rustc_driver::Compilation;
    use rustc_interface::interface::{Compiler, Config};

    const CONST_AGGREGATE_RETURN_SHAPES_SOURCE: &str = r#"
#![feature(core_intrinsics)]
#![allow(internal_features)]

const ARR: [i32; 2] = [4, 5];
pub struct PlainStruct { x: i32, y: i32 }
pub struct TupleStruct(i32, i32);
pub enum EmptyEnum { A, B }
pub enum PairEnum { Pair(i32, i32), Empty }
pub enum TaggedPairEnum { Empty, Pair(i32, i32) }
pub fn char_return() -> char { 'A' }
pub fn unit_return() -> () { () }
pub fn tuple_char() -> (char, i32) { ('A', 1) }
pub fn tuple_unit_i32() -> ((), i32) { ((), 1) }
pub fn empty_enum_a() -> EmptyEnum { EmptyEnum::A }
pub fn empty_enum_b() -> EmptyEnum { EmptyEnum::B }
pub fn option_none() -> Option<i32> { None }
pub fn option_some() -> Option<i32> { Some(1) }
pub fn result_ok() -> Result<i32, i32> { Ok(1) }
pub fn result_err() -> Result<i32, i32> { Err(2) }
pub fn array_from_named_const() -> [i32; 2] { ARR }
pub fn plain_struct() -> PlainStruct { PlainStruct { x: 3, y: 4 } }
pub fn tuple_struct() -> TupleStruct { TupleStruct(7, 8) }
pub fn pair_enum() -> PairEnum { PairEnum::Pair(9, 10) }
pub fn tagged_pair_enum() -> TaggedPairEnum { TaggedPairEnum::Pair(11, 12) }
pub fn small_array() -> [i32; 2] { [5, 6] }
pub fn str_literal_return() -> &'static str { "trust_str_fixture" }
pub fn double_ref_str() -> &'static &'static str { &"trust_double_ref" }
pub fn byte_array_ref_return() -> &'static [u8; 10] { b"\x07prefix \xc0\x00" }
pub fn str_array_ref_return() -> &'static [&'static str; 2] { &["pa", "pb"] }

pub mod intrinsics {
    #[inline(never)]
    pub fn ctpop(x: u8) -> u32 { x as u32 }
    #[inline(never)]
    pub fn cttz(x: u8) -> u32 { x as u32 }
    #[inline(never)]
    pub fn ctlz(x: u8) -> u32 { x as u32 }
    #[inline(never)]
    pub fn bswap(x: u8) -> u8 { x }
    #[inline(never)]
    pub fn bitreverse(x: u8) -> u8 { x }
}

#[inline(never)]
pub fn compiler_intrinsic_ctpop(x: u8) -> u32 { core::intrinsics::ctpop(x) }
#[inline(never)]
pub fn compiler_intrinsic_cttz(x: u8) -> u32 { core::intrinsics::cttz(x) }
#[inline(never)]
pub fn compiler_intrinsic_ctlz(x: u8) -> u32 { core::intrinsics::ctlz(x) }
#[inline(never)]
pub fn compiler_intrinsic_bswap(x: u8) -> u8 { core::intrinsics::bswap(x) }
#[inline(never)]
pub fn compiler_intrinsic_bitreverse(x: u8) -> u8 { core::intrinsics::bitreverse(x) }

#[inline(never)]
pub fn source_spelled_intrinsics_ctpop(x: u8) -> u32 { intrinsics::ctpop(x) }
#[inline(never)]
pub fn source_spelled_intrinsics_cttz(x: u8) -> u32 { intrinsics::cttz(x) }
#[inline(never)]
pub fn source_spelled_intrinsics_ctlz(x: u8) -> u32 { intrinsics::ctlz(x) }
#[inline(never)]
pub fn source_spelled_intrinsics_bswap(x: u8) -> u8 { intrinsics::bswap(x) }
#[inline(never)]
pub fn source_spelled_intrinsics_bitreverse(x: u8) -> u8 { intrinsics::bitreverse(x) }

// v24 direct-call unwind-exemption fixture: `direct_call_add` makes a DIRECT
// call to `add_helper`. `add_helper` divides (an always-checked div-by-zero /
// INT_MIN÷-1 panic), so it MAY unwind, and the caller has no drop-carrying
// locals — so rustc lowers the call with `unwind: Continue` (the ordinary
// panic-propagation edge). `#[inline(never)]` keeps the call from being inlined
// away at `-Zmir-opt-level=3`, so the Call terminator survives to be inspected.
#[inline(never)]
pub fn add_helper(a: i32, b: i32) -> i32 { a / b }
pub fn direct_call_add(a: i32, b: i32) -> i32 { add_helper(a, b) }
"#;
    const TEST_CRATE_PATH: &str = "return_shapes.rs";

    const CAST_SOURCE: &str = r#"
#![feature(auto_traits, const_trait_impl, intrinsics, lang_items, no_core, rustc_attrs, unboxed_closures)]
#![no_core]

#[lang = "sized"]
pub trait Sized: MetaSized {}

#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}

#[lang = "pointee_sized"]
pub trait PointeeSized {}

#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
impl<T: PointeeSized> LegacyReceiver for &mut T {}

#[lang = "tuple_trait"]
pub trait Tuple {}

#[lang = "fn_once"]
pub trait FnOnce<Args: Tuple> {
    #[lang = "fn_once_output"]
    type Output;

    extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
}

#[lang = "fn_mut"]
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output;
}

#[lang = "fn"]
pub trait Fn<Args: Tuple>: FnMut<Args> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output;
}

#[lang = "unsize"]
pub trait Unsize<T: PointeeSized>: PointeeSized {}

#[lang = "coerce_unsized"]
pub trait CoerceUnsized<T: PointeeSized> {}

impl<'a, 'b: 'a, T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<&'a U> for &'b T {}
impl<T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<*const U> for *const T {}

#[lang = "copy"]
pub trait Copy: Clone {}

#[lang = "clone"]
pub trait Clone {}

#[lang = "freeze"]
pub unsafe auto trait Freeze {}

#[lang = "destruct"]
pub const trait Destruct: PointeeSized {}

#[rustc_intrinsic]
pub const unsafe fn transmute<Src, Dst>(src: Src) -> Dst;

pub fn ptr_to_ptr(p: *const u8) -> *const u32 { p as *const u32 }

pub fn array_ref_to_slice_ref(a: &[u8; 4]) -> &[u8] { a }

pub fn array_raw_ptr_to_slice_raw_ptr(p: *const [u8; 4]) -> *const [u8] { p }

fn helper_fn_item() -> i32 { 7 }

pub fn function_item_to_fn_pointer() -> fn() -> i32 { helper_fn_item }

pub fn function_pointer_to_unsafe(f: fn() -> i32) -> unsafe fn() -> i32 { f }

pub fn closure_to_fn_pointer() -> fn(i32) -> i32 { |x| x }

pub unsafe fn transmute_u32_bytes(x: u32) -> [u8; 4] {
    unsafe { transmute::<u32, [u8; 4]>(x) }
}
"#;
    const CAST_TEST_CRATE_PATH: &str = "casts.rs";

    // A non-capturing closure handed to a generic iterator adapter
    // (`.map(|x| ...)`) materializes in MIR as a `Const` of `TyKind::Closure`.
    // This is the `sum_doubled` shape that used to stamp a spurious Unknown on
    // every closure-passing function. Compiled standalone so the closure const
    // is reachable without perturbing the return-shape fixture's single-`_0`
    // assignment invariant (this fn returns via a `sum()` call, not an assign).
    const CLOSURE_SOURCE: &str = r#"
pub fn closure_map_sum(s: &[u32]) -> u32 {
    s.iter().map(|x| x.wrapping_mul(2)).sum()
}

pub fn closure_map_sum_other(s: &[u32]) -> u32 {
    s.iter().map(|x| x.wrapping_mul(3)).sum()
}
"#;
    const CLOSURE_TEST_CRATE_PATH: &str = "closures.rs";

    const ZST_CONST_OPERAND_SOURCE: &str = r#"
#![feature(auto_traits, lang_items, no_core)]
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

pub struct LocalZst;
pub struct OtherZst;
pub enum EnumZst { A, B }

#[inline(never)]
pub fn consume_zst<T>(_x: T) -> i32 { 1 }

fn helper_fn_item() -> i32 { 2 }
fn helper_fn_item_other() -> i32 { 3 }

pub fn pass_local_zst() -> i32 { consume_zst(LocalZst) }
pub fn pass_other_zst() -> i32 { consume_zst(OtherZst) }
pub fn pass_enum_zst() -> i32 { consume_zst(EnumZst::A) }
pub fn pass_function_item() -> i32 { consume_zst(helper_fn_item) }
pub fn pass_function_item_other() -> i32 { consume_zst(helper_fn_item_other) }
"#;
    const ZST_CONST_OPERAND_TEST_CRATE_PATH: &str = "zst_const_operands.rs";

    struct InMemoryFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(TEST_CRATE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CONST_AGGREGATE_RETURN_SHAPES_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected test file path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in convert.rs tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryCastFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryCastFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CAST_TEST_CRATE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CAST_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected cast test file path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in cast tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryClosureFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryClosureFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(CLOSURE_TEST_CRATE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(CLOSURE_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected closure test file path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in closure tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    struct InMemoryZstConstOperandFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryZstConstOperandFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(ZST_CONST_OPERAND_TEST_CRATE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(ZST_CONST_OPERAND_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected zst const operand test file path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in zst const operand tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    #[derive(Default)]
    struct CompilerResults {
        rvalues: BTreeMap<String, Rvalue>,
        statements: BTreeMap<String, Statement>,
        terminators: BTreeMap<String, Terminator>,
        return_types: BTreeMap<String, Ty>,
        direct_callees: BTreeMap<String, Vec<String>>,

        /// v24: raw `mir::UnwindAction` name (e.g. "Continue") for a compiled
        /// function's first `Call` terminator, so the direct-call unwind-exemption
        /// test can assert the fixture truly exercises the `Continue` edge.
        call_unwind_actions: BTreeMap<String, String>,
    }

    struct ReturnShapeCallbacks {
        results: CompilerResults,
    }

    struct CastCallbacks {
        rvalues: BTreeMap<String, Rvalue>,
    }

    impl rustc_driver::Callbacks for ReturnShapeCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            let wrap_operand = mir::Operand::Copy(mir::Place::from(mir::Local::from_usize(1)));
            let wrap_rvalue = mir::Rvalue::WrapUnsafeBinder(wrap_operand, tcx.types.i32);
            self.results.rvalues.insert(
                "__synthetic_wrap_unsafe_binder".to_string(),
                convert_rvalue(tcx, &wrap_rvalue, None, None),
            );

            for (name, borrow_kind) in synthetic_ref_borrow_kinds() {
                let ref_rvalue = mir::Rvalue::Ref(
                    tcx.lifetimes.re_erased,
                    borrow_kind,
                    mir::Place::from(mir::Local::from_usize(1)),
                );
                self.results.rvalues.insert(name, convert_rvalue(tcx, &ref_rvalue, None, None));
            }

            for (name, stmt) in synthetic_analysis_only_statements() {
                self.results.statements.insert(name, convert_statement(tcx, &stmt, None, None));
            }

            for (name, terminator) in synthetic_metadata_terminators() {
                self.results.terminators.insert(name, convert_terminator(tcx, &terminator, None));
            }

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    if fn_name.starts_with("compiler_intrinsic_")
                        || fn_name.starts_with("source_spelled_intrinsics_")
                    {
                        let callees = body
                            .basic_blocks
                            .iter()
                            .filter_map(|block| match &block.terminator().kind {
                                mir::TerminatorKind::Call { func, .. } => {
                                    Some(func_operand_name(tcx, func))
                                }
                                _ => None,
                            })
                            .collect();
                        self.results.direct_callees.insert(fn_name, callees);
                        continue;
                    }
                    // v24: the direct-call fixture is inspected ONLY for its `Call`
                    // TERMINATOR (unwind-exemption pin), not a return-place rvalue —
                    // its `_0` is initialized by the call destination, not an `Assign`
                    // statement, so `extract_return_place_rvalue` would fail its
                    // single-`_0`-assign invariant. Capture the terminator + raw
                    // unwind action and skip the return-shape extraction for it.
                    if fn_name == "direct_call_add" {
                        if let Some((unwind, term)) = extract_first_call_terminator(tcx, body) {
                            self.results.call_unwind_actions.insert(fn_name.clone(), unwind);
                            self.results.terminators.insert(fn_name, term);
                        }
                        continue;
                    }
                    self.results
                        .rvalues
                        .insert(fn_name.clone(), extract_return_place_rvalue(tcx, body, &fn_name));
                    // Trust: M6 rung-7 sweep — a real `body` is in scope here, so use its
                    // own `typing_env` (matching `extract_return_place_rvalue`'s existing
                    // convention below) instead of the plain env-less `convert_ty`.
                    self.results.return_types.insert(
                        fn_name,
                        ty_convert::convert_ty_in_env(tcx, body.typing_env(tcx), body.return_ty()),
                    );
                }
            }

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for CastCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryCastFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    if !matches!(
                        fn_name.as_str(),
                        "ptr_to_ptr"
                            | "array_ref_to_slice_ref"
                            | "array_raw_ptr_to_slice_raw_ptr"
                            | "closure_to_fn_pointer"
                            | "function_item_to_fn_pointer"
                            | "function_pointer_to_unsafe"
                            | "transmute_u32_bytes"
                    ) {
                        continue;
                    }
                    let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                    self.rvalues
                        .insert(fn_name.clone(), extract_return_place_rvalue(tcx, body, &fn_name));
                }
            }

            let operand = mir::Operand::Copy(mir::Place::from(mir::Local::from_usize(1)));
            for (name, coercion) in [
                ("__synthetic_mut_to_const_pointer_coercion", PointerCoercion::MutToConstPointer),
                ("__synthetic_array_to_pointer_coercion", PointerCoercion::ArrayToPointer),
            ] {
                let rvalue = mir::Rvalue::Cast(
                    mir::CastKind::PointerCoercion(coercion, mir::CoercionSource::Implicit),
                    operand.clone(),
                    ty::Ty::new_imm_ptr(tcx, tcx.types.u8),
                );
                self.rvalues.insert(name.to_string(), convert_rvalue(tcx, &rvalue, None, None));
            }

            Compilation::Stop
        }
    }

    struct ClosureCallbacks {
        operands: BTreeMap<String, Operand>,
        capturing_operands: BTreeMap<String, Operand>,
        aggregates: BTreeMap<String, Rvalue>,
    }

    struct ZstConstOperandCallbacks {
        call_args: BTreeMap<String, Vec<Operand>>,
    }

    impl rustc_driver::Callbacks for ClosureCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryClosureFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                if let rustc_hir::ItemKind::Fn { ident, .. } = item.kind {
                    let fn_name = ident.name.to_string();
                    let (operand, capturing, aggregate) =
                        extract_closure_test_values(tcx, item.owner_id.def_id);
                    if let Some(operand) = operand {
                        self.operands.insert(fn_name.clone(), operand);
                    }
                    if let Some(capturing) = capturing {
                        self.capturing_operands.insert(ident.name.to_string(), capturing);
                    }
                    if let Some(aggregate) = aggregate {
                        self.aggregates.insert(fn_name, aggregate);
                    }
                }
            }

            Compilation::Stop
        }
    }

    impl rustc_driver::Callbacks for ZstConstOperandCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryZstConstOperandFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            tcx.sess.dcx().abort_if_errors();

            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                let rustc_hir::ItemKind::Fn { ident, .. } = item.kind else {
                    continue;
                };
                let fn_name = ident.name.to_string();
                if !fn_name.starts_with("pass_") {
                    continue;
                }
                let body = tcx.optimized_mir(item.owner_id.def_id.to_def_id());
                if let Some(args) = extract_first_call_args(tcx, body) {
                    self.call_args.insert(fn_name, args);
                }
            }

            Compilation::Stop
        }
    }

    /// Inventory both real authored closure aggregates and closure-typed Const
    /// operands. The aggregate is converted through the production rvalue
    /// path; its compiler-owned DefId/args also seed a test-only zero-sized
    /// Const for the independent `convert_const_operand` seam. Real optimized
    /// Const operands retain the compiler-generated capturing-adapter negative.
    struct ClosureConstFinder<'tcx> {
        tcx: TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        found: Option<Operand>,
        capturing: Option<Operand>,
        aggregate: Option<Rvalue>,
    }

    impl<'tcx> mir::visit::Visitor<'tcx> for ClosureConstFinder<'tcx> {
        fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
            if let mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(def_id, args), operands) =
                rvalue
            {
                let closure_args = args.as_closure();
                if operands.is_empty() && closure_args.upvar_tys().is_empty() {
                    // Elaborated MIR represents the authored
                    // noncapturing callback as its real zero-upvar aggregate.
                    // Preserve that production conversion independently.
                    if self.aggregate.is_none() {
                        self.aggregate =
                            Some(convert_rvalue(self.tcx, rvalue, None, Some(self.typing_env)));
                    }

                    // Unit-test construction only: exercise the separate
                    // `convert_const_operand` seam with the semantically
                    // equivalent zero-sized closure Const built from this
                    // compiler-owned DefId/args. Production traversal does not
                    // manufacture or substitute a Const for the aggregate.
                    if self.found.is_none() {
                        let closure_ty = ty::Ty::new_closure(self.tcx, *def_id, *args);
                        let operand =
                            mir::Operand::zero_sized_constant(closure_ty, rustc_span::DUMMY_SP);
                        let mir::Operand::Constant(constant) = operand else {
                            unreachable!("zero_sized_constant always yields Operand::Constant")
                        };
                        self.found = Some(convert_const_operand(self.tcx, &constant));
                    }
                }
            }
            self.super_rvalue(rvalue, location);
        }

        fn visit_const_operand(
            &mut self,
            constant: &mir::ConstOperand<'tcx>,
            _location: mir::Location,
        ) {
            if matches!(constant.const_.ty().kind(), ty::TyKind::Closure(..)) {
                // Optimized iterator MIR also contains compiler-generated
                // capturing adapter closures (for example `map_fold`). Those
                // correctly lower to Unsupported and are not the source
                // upvar-free callback this fixture is testing. Keep walking
                // until conversion yields an identity-bearing closure value.
                let converted = convert_const_operand(self.tcx, constant);
                if matches!(
                    &converted,
                    Operand::Constant(ConstValue::CallableItem { kind: CallableKind::Closure, .. })
                ) && self.found.is_none()
                {
                    self.found = Some(converted);
                } else if matches!(
                    &converted,
                    Operand::Unsupported { kind, .. } if kind == "Const::Closure"
                ) && self.capturing.is_none()
                {
                    self.capturing = Some(converted);
                }
            }
        }
    }

    fn extract_closure_test_values<'tcx>(
        tcx: TyCtxt<'tcx>,
        local_def_id: rustc_span::def_id::LocalDefId,
    ) -> (Option<Operand>, Option<Operand>, Option<Rvalue>) {
        use mir::visit::Visitor as _;
        let elaborated = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
        let mut finder = {
            let body = elaborated.borrow();
            let mut finder = ClosureConstFinder {
                tcx,
                typing_env: body.typing_env(tcx),
                found: None,
                capturing: None,
                aggregate: None,
            };
            finder.visit_body(&body);
            finder
        };

        // Optimized iterator MIR supplies the separate compiler-generated
        // capturing-adapter negative. Borrowing elaborated MIR above is scoped
        // and released before this query legitimately steals it.
        let optimized = tcx.optimized_mir(local_def_id.to_def_id());
        finder.typing_env = optimized.typing_env(tcx);
        finder.visit_body(optimized);
        (finder.found, finder.capturing, finder.aggregate)
    }

    fn compiler_sysroot() -> String {
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
        candidate.join("bin/trustc").is_file() && sysroot_has_host_std(candidate)
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

    fn compile_extract_test_results() -> CompilerResults {
        let mut callbacks = ReturnShapeCallbacks { results: CompilerResults::default() };
        let mut args = vec![
            "rustc".to_string(),
            TEST_CRATE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_convert_return_shapes".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            // These fixtures stop in `after_analysis`; loading a dylib codegen
            // backend is unnecessary and makes the test process depend on a
            // separately assembled compiler sysroot.  The in-process backend
            // loader is intentionally one-shot, so a failed dylib probe also
            // poisons every later fixture in this test binary.  The built-in
            // dummy backend is the rustc-supported analysis-only route.
            "-Zcodegen-backend=dummy".to_string(),
            // These fixtures exercise extraction, not the batteries-on Trust
            // verification pass. Unsupported shapes are intentional inputs.
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile const aggregate return-shape test crate");

        callbacks.results
    }

    fn extract_test_results() -> &'static CompilerResults {
        static RESULTS: OnceLock<CompilerResults> = OnceLock::new();
        RESULTS.get_or_init(compile_extract_test_results)
    }

    fn compile_cast_test_rvalues() -> BTreeMap<String, Rvalue> {
        let mut callbacks = CastCallbacks { rvalues: BTreeMap::new() };
        let args = vec![
            "rustc".to_string(),
            CAST_TEST_CRATE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_casts".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
            "-Aunnecessary_transmutes".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile no_core cast test crate");

        callbacks.rvalues
    }

    fn cast_test_rvalues() -> &'static BTreeMap<String, Rvalue> {
        static RESULTS: OnceLock<BTreeMap<String, Rvalue>> = OnceLock::new();
        RESULTS.get_or_init(compile_cast_test_rvalues)
    }

    struct ClosureTestOperands {
        callable: BTreeMap<String, Operand>,
        capturing: BTreeMap<String, Operand>,
        aggregates: BTreeMap<String, Rvalue>,
    }

    fn compile_closure_test_operands() -> ClosureTestOperands {
        let mut callbacks = ClosureCallbacks {
            operands: BTreeMap::new(),
            capturing_operands: BTreeMap::new(),
            aggregates: BTreeMap::new(),
        };
        let mut args = vec![
            "rustc".to_string(),
            CLOSURE_TEST_CRATE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_closures".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile closure const test crate");

        ClosureTestOperands {
            callable: callbacks.operands,
            capturing: callbacks.capturing_operands,
            aggregates: callbacks.aggregates,
        }
    }

    fn closure_test_operands() -> &'static BTreeMap<String, Operand> {
        &closure_test_results().callable
    }

    fn closure_test_results() -> &'static ClosureTestOperands {
        static RESULTS: OnceLock<ClosureTestOperands> = OnceLock::new();
        RESULTS.get_or_init(compile_closure_test_operands)
    }

    fn compile_zst_const_operand_call_args() -> BTreeMap<String, Vec<Operand>> {
        let mut callbacks = ZstConstOperandCallbacks { call_args: BTreeMap::new() };
        // This is a self-contained no_core fixture; requiring a staged sysroot
        // would make it depend on unrelated std assembly.
        let args = vec![
            "rustc".to_string(),
            ZST_CONST_OPERAND_TEST_CRATE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_zst_const_operands".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            "-Zmir-opt-level=3".to_string(),
            "-Zno-codegen".to_string(),
            "-Zcodegen-backend=dummy".to_string(),
            "-Ztrust-verify=off".to_string(),
            "-Ainternal_features".to_string(),
        ];

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(result.is_ok(), "failed to compile zst const operand test crate");

        callbacks.call_args
    }

    fn zst_const_operand_call_args() -> &'static BTreeMap<String, Vec<Operand>> {
        static RESULTS: OnceLock<BTreeMap<String, Vec<Operand>>> = OnceLock::new();
        RESULTS.get_or_init(compile_zst_const_operand_call_args)
    }

    fn const_aggregate_return_shapes() -> &'static BTreeMap<String, Rvalue> {
        &extract_test_results().rvalues
    }

    fn fixture_return_types() -> &'static BTreeMap<String, Ty> {
        &extract_test_results().return_types
    }

    fn synthetic_statement_shapes() -> &'static BTreeMap<String, Statement> {
        &extract_test_results().statements
    }

    fn synthetic_terminator_shapes() -> &'static BTreeMap<String, Terminator> {
        &extract_test_results().terminators
    }

    fn fixture_direct_callees() -> &'static BTreeMap<String, Vec<String>> {
        &extract_test_results().direct_callees
    }

    fn extract_return_place_rvalue<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        fn_name: &str,
    ) -> Rvalue {
        let return_assignments = body
            .basic_blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .filter_map(|stmt| match &stmt.kind {
                mir::StatementKind::Assign(box (place, rvalue))
                    if place.local == mir::RETURN_PLACE =>
                {
                    Some(convert_rvalue(
                        tcx,
                        rvalue,
                        Some(&body.local_decls),
                        Some(body.typing_env(tcx)),
                    ))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        // Optimized MIR may elide `_0 = ()` entirely because the unit return
        // place carries no data. Reconstruct only that uniquely determined ZST
        // value; every non-unit body retains the exact single-assignment
        // invariant below so a missing or duplicated executable value still
        // fails the fixture closed.
        if return_assignments.is_empty() && body.return_ty().is_unit() {
            return Rvalue::Use(Operand::Constant(ConstValue::Unit));
        }

        assert_eq!(
            return_assignments.len(),
            1,
            "expected a single `_0` assignment in optimized MIR for `{fn_name}`, got {return_assignments:?}",
        );
        return_assignments.into_iter().next().unwrap()
    }

    /// v24: find the first `Call` terminator in a compiled body and return both its
    /// raw `mir::UnwindAction` name and the converted TrustIr `Terminator`. Used to
    /// pin that a DIRECT call carrying `unwind: Continue` lowers to a STRUCTURED
    /// `Call` routed to its success target (the exemption), not an Opaque fail-close.
    fn extract_first_call_terminator<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> Option<(String, Terminator)> {
        body.basic_blocks.iter().find_map(|bb| {
            let term = bb.terminator();
            let mir::TerminatorKind::Call { unwind, .. } = &term.kind else {
                return None;
            };
            let unwind_name = match unwind {
                mir::UnwindAction::Continue => "Continue",
                mir::UnwindAction::Unreachable => "Unreachable",
                mir::UnwindAction::Terminate(_) => "Terminate",
                mir::UnwindAction::Cleanup(_) => "Cleanup",
            }
            .to_string();
            Some((unwind_name, convert_terminator(tcx, term, Some(body.typing_env(tcx)))))
        })
    }

    fn extract_first_call_args<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> Option<Vec<Operand>> {
        body.basic_blocks.iter().find_map(|bb| {
            let terminator = bb.terminator();
            let Terminator::Call { args, .. } =
                convert_terminator(tcx, terminator, Some(body.typing_env(tcx)))
            else {
                return None;
            };
            Some(args)
        })
    }

    fn assert_constant_int_operand(operand: &Operand, expected: i128) {
        match operand {
            Operand::Constant(ConstValue::Int(value)) => assert_eq!(*value, expected),
            other => panic!("expected integer constant operand, got {other:?}"),
        }
    }

    fn assert_constant_uint_operand(operand: &Operand, expected: u128, expected_width: u32) {
        match operand {
            Operand::Constant(ConstValue::Uint(value, width)) => {
                assert_eq!(*value, expected);
                assert_eq!(*width, expected_width);
            }
            other => panic!("expected unsigned integer constant operand, got {other:?}"),
        }
    }

    fn assert_unit_operand(operand: &Operand) {
        assert!(matches!(operand, Operand::Constant(ConstValue::Unit)));
    }

    fn local_operand<'tcx>(local: usize) -> mir::Operand<'tcx> {
        mir::Operand::Copy(mir::Place::from(mir::Local::from_usize(local)))
    }

    fn synthetic_stmt<'tcx>(kind: mir::StatementKind<'tcx>) -> mir::Statement<'tcx> {
        mir::Statement::new(mir::SourceInfo::outermost(rustc_span::DUMMY_SP), kind)
    }

    fn synthetic_terminator<'tcx>(kind: mir::TerminatorKind<'tcx>) -> mir::Terminator<'tcx> {
        mir::Terminator {
            source_info: mir::SourceInfo::outermost(rustc_span::DUMMY_SP),
            kind,
            // 1.99 migration: terminators grew MIR-level attributes; synthetic
            // test terminators carry none.
            attributes: Default::default(),
        }
    }

    fn synthetic_analysis_only_statements<'tcx>() -> BTreeMap<String, mir::Statement<'tcx>> {
        let mut statements = BTreeMap::new();

        statements.insert(
            "fake_read".to_string(),
            synthetic_stmt(mir::StatementKind::FakeRead(Box::new((
                mir::FakeReadCause::ForMatchedPlace(None),
                mir::Place::from(mir::Local::from_usize(1)),
            )))),
        );

        statements.insert(
            "ascribe_user_type".to_string(),
            synthetic_stmt(mir::StatementKind::AscribeUserType(
                Box::new((
                    mir::Place::from(mir::Local::from_usize(2)),
                    mir::UserTypeProjection {
                        base: ty::UserTypeAnnotationIndex::from_usize(0),
                        projs: vec![],
                    },
                )),
                ty::Variance::Invariant,
            )),
        );

        statements.insert(
            "backward_incompatible_drop_hint".to_string(),
            synthetic_stmt(mir::StatementKind::BackwardIncompatibleDropHint {
                place: Box::new(mir::Place::from(mir::Local::from_usize(3))),
                reason: mir::BackwardIncompatibleDropReason::Edition2024,
            }),
        );

        statements
    }

    fn synthetic_ref_borrow_kinds() -> Vec<(String, mir::BorrowKind)> {
        vec![
            ("__synthetic_ref_shared".to_string(), mir::BorrowKind::Shared),
            (
                "__synthetic_ref_mut_default".to_string(),
                mir::BorrowKind::Mut { kind: mir::MutBorrowKind::Default },
            ),
            (
                "__synthetic_ref_mut_two_phase".to_string(),
                mir::BorrowKind::Mut { kind: mir::MutBorrowKind::TwoPhaseBorrow },
            ),
            (
                "__synthetic_ref_mut_closure_capture".to_string(),
                mir::BorrowKind::Mut { kind: mir::MutBorrowKind::ClosureCapture },
            ),
            (
                "__synthetic_ref_fake_shallow".to_string(),
                mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow),
            ),
            (
                "__synthetic_ref_fake_deep".to_string(),
                mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep),
            ),
        ]
    }

    fn synthetic_metadata_terminators<'tcx>() -> BTreeMap<String, mir::Terminator<'tcx>> {
        let mut terminators = BTreeMap::new();

        terminators.insert(
            "false_edge".to_string(),
            synthetic_terminator(mir::TerminatorKind::FalseEdge {
                real_target: mir::BasicBlock::from_usize(7),
                imaginary_target: mir::BasicBlock::from_usize(9),
            }),
        );

        terminators.insert(
            "false_unwind".to_string(),
            synthetic_terminator(mir::TerminatorKind::FalseUnwind {
                real_target: mir::BasicBlock::from_usize(11),
                unwind: mir::UnwindAction::Cleanup(mir::BasicBlock::from_usize(13)),
            }),
        );

        terminators.insert(
            "coroutine_drop".to_string(),
            synthetic_terminator(mir::TerminatorKind::CoroutineDrop),
        );

        terminators.insert(
            "unwind_resume".to_string(),
            synthetic_terminator(mir::TerminatorKind::UnwindResume),
        );

        terminators.insert(
            "unwind_terminate".to_string(),
            synthetic_terminator(mir::TerminatorKind::UnwindTerminate(
                mir::UnwindTerminateReason::Abi,
            )),
        );

        // An ordinary overflow/bounds Assert carries Continue when panic
        // propagates to the caller. The assertion itself must remain
        // structured so its exact success condition becomes the safety VC.
        terminators.insert(
            "assert_continue".to_string(),
            synthetic_terminator(mir::TerminatorKind::Assert {
                cond: local_operand(1),
                expected: true,
                msg: Box::new(mir::AssertKind::Overflow(
                    mir::BinOp::Add,
                    local_operand(1),
                    local_operand(2),
                )),
                target: mir::BasicBlock::from_usize(5),
                unwind: mir::UnwindAction::Continue,
            }),
        );

        // v24: the Call unwind exemption applies to DIRECT calls (routed to their
        // success target — see the compiled `direct_call_add` fixture). This
        // synthetic case is an INDIRECT call (`func` is a local Copy, NOT a `FnDef`),
        // which the exemption deliberately does NOT open: with the unwind fail-close
        // gone it now falls to the indirect fail-close instead, staying Opaque with
        // kind `Call(indirect)`. Pin that indirect calls remain fail-closed.
        terminators.insert(
            "call_continue".to_string(),
            synthetic_terminator(mir::TerminatorKind::Call {
                func: local_operand(1),
                args: Box::default(),
                destination: mir::Place::from(mir::Local::from_usize(0)),
                target: Some(mir::BasicBlock::from_usize(5)),
                unwind: mir::UnwindAction::Continue,
                call_source: mir::CallSource::Normal,
                fn_span: rustc_span::DUMMY_SP,
            }),
        );

        terminators
    }

    fn assert_adt_name(name: &str, expected_suffix: &str) {
        assert!(
            name.ends_with(expected_suffix),
            "expected ADT path ending with `{expected_suffix}`, got `{name}`",
        );
    }

    /// Helper: build args with a Copy operand as the first arg (pointer place).
    fn ptr_args() -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1))]
    }

    /// Helper: build args with two operands (ptr + value).
    fn ptr_val_args() -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(42, 64))]
    }

    /// Helper: build args for CAS (ptr, old, new).
    fn cas_args() -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 64)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        ]
    }

    fn ordering_arg(ordering: AtomicOrdering) -> Operand {
        let discr = match ordering {
            AtomicOrdering::Relaxed => 0,
            AtomicOrdering::Release => 1,
            AtomicOrdering::Acquire => 2,
            AtomicOrdering::AcqRel => 3,
            AtomicOrdering::SeqCst => 4,
            _ => 4,
        };
        Operand::Constant(ConstValue::Uint(discr, 64))
    }

    fn ptr_order_args(ordering: AtomicOrdering) -> Vec<Operand> {
        vec![Operand::Copy(Place::local(1)), ordering_arg(ordering)]
    }

    fn ptr_val_order_args(ordering: AtomicOrdering) -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(42, 64)),
            ordering_arg(ordering),
        ]
    }

    fn cas_order_args(success: AtomicOrdering, failure: AtomicOrdering) -> Vec<Operand> {
        vec![
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 64)),
            Operand::Constant(ConstValue::Uint(1, 64)),
            ordering_arg(success),
            ordering_arg(failure),
        ]
    }

    fn fence_order_args(ordering: AtomicOrdering) -> Vec<Operand> {
        vec![ordering_arg(ordering)]
    }

    fn default_dest() -> Place {
        Place::local(0)
    }

    fn default_span() -> SourceSpan {
        SourceSpan::default()
    }

    fn assert_malformed_atomic_metadata(func_name: &str, args: &[Operand], expected_detail: &str) {
        let parsed =
            parse_atomic_intrinsic_metadata(func_name, args, &default_dest(), &default_span());
        assert!(
            matches!(
                parsed,
                AtomicIntrinsicMetadata::Malformed { ref detail }
                    if detail.contains(expected_detail)
            ),
            "{func_name} must be recognized as malformed atomic metadata containing \
             {expected_detail:?}, got {parsed:?}"
        );
    }

    // --- Form A: load ---

    #[test]
    fn form_a_load_seqcst() {
        let result = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        );
        let op = result.expect("should detect atomic load");
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.failure_ordering.is_none());
        assert!(op.dest.is_some());
        assert_eq!(op.place, Place::local(1));
    }

    #[test]
    fn form_a_load_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_acquire",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_load_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: store ---

    #[test]
    fn form_a_store_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_release",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none(), "store has no return value");
    }

    #[test]
    fn form_a_store_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_store_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_store_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    // --- Form A: exchange ---

    #[test]
    fn form_a_xchg_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xchg_acqrel",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert!(op.dest.is_some());
    }

    // --- Form A: compare_exchange ---

    #[test]
    fn form_a_cxchg_seqcst_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_seqcst_seqcst",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::SeqCst));
    }

    #[test]
    fn form_a_cxchg_acqrel_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_acqrel_acquire",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn form_a_cxchg_release_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchg_release_relaxed",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: compare_exchange_weak ---

    #[test]
    fn form_a_cxchgweak_acquire_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_cxchgweak_acquire_relaxed",
            &cas_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchangeWeak);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Relaxed));
    }

    // --- Form A: fetch operations ---

    #[test]
    fn form_a_xadd_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xadd_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_a_xsub_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xsub_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchSub);
        assert_eq!(op.ordering, AtomicOrdering::Relaxed);
    }

    #[test]
    fn form_a_and_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_and_acquire",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAnd);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_or_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_or_release",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchOr);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_xor_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_xor_acqrel",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchXor);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    #[test]
    fn form_a_nand_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_nand_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchNand);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_a_min_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_min_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_max_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_max_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    #[test]
    fn form_a_umin_relaxed() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umin_relaxed",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMin);
    }

    #[test]
    fn form_a_umax_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_umax_seqcst",
            &ptr_val_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchMax);
    }

    // --- Form A: fence ---

    #[test]
    fn form_a_fence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none(), "fence has no return value");
        assert_eq!(op.place, Place::local(0), "fence has synthetic place");
    }

    #[test]
    fn form_a_fence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acquire",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_a_fence_release() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_release",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn form_a_fence_acqrel() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_fence_acqrel",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
    }

    // --- Form A: singlethreadfence (compiler_fence) ---

    #[test]
    fn form_a_singlethreadfence_seqcst() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_seqcst",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_a_singlethreadfence_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_singlethreadfence_acquire",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    // --- Form A: consume ordering maps to acquire ---

    #[test]
    fn form_a_load_consume_maps_to_acquire() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_consume",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire, "Consume maps to Acquire");
    }

    // --- Form B: generic atomic calls ---

    #[test]
    fn form_b_atomic_load() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::atomic::atomic_load",
            &ptr_order_args(AtomicOrdering::Acquire),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Load);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn form_b_atomic_store() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_store",
            &ptr_val_order_args(AtomicOrdering::Release),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Store);
        assert_eq!(op.ordering, AtomicOrdering::Release);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_b_atomic_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_exchange",
            &ptr_val_order_args(AtomicOrdering::AcqRel),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Exchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert!(op.dest.is_some());
    }

    #[test]
    fn form_b_atomic_compare_exchange() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_compare_exchange",
            &cas_order_args(AtomicOrdering::AcqRel, AtomicOrdering::Acquire),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompareExchange);
        assert_eq!(op.ordering, AtomicOrdering::AcqRel);
        assert_eq!(op.failure_ordering, Some(AtomicOrdering::Acquire));
    }

    #[test]
    fn form_b_atomic_fetch_add() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fetch_add",
            &ptr_val_order_args(AtomicOrdering::SeqCst),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::FetchAdd);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
    }

    #[test]
    fn form_b_atomic_fence() {
        let op = parse_atomic_intrinsic(
            "core::sync::atomic::atomic::atomic_fence",
            &fence_order_args(AtomicOrdering::SeqCst),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::SeqCst);
        assert!(op.dest.is_none());
    }

    #[test]
    fn form_b_atomic_load_missing_ordering_is_malformed() {
        let parsed = parse_atomic_intrinsic_metadata(
            "std::sync::atomic::atomic::atomic_load",
            &ptr_args(),
            &default_dest(),
            &default_span(),
        );
        assert!(matches!(
            parsed,
            AtomicIntrinsicMetadata::Malformed { detail }
                if detail.contains("load ordering argument")
        ));
    }

    #[test]
    fn form_b_atomic_compare_exchange_missing_failure_ordering_is_malformed() {
        let parsed = parse_atomic_intrinsic_metadata(
            "core::sync::atomic::atomic::atomic_compare_exchange",
            &cas_order_args(AtomicOrdering::SeqCst, AtomicOrdering::Relaxed)[..4],
            &default_dest(),
            &default_span(),
        );
        assert!(matches!(
            parsed,
            AtomicIntrinsicMetadata::Malformed { detail }
                if detail.contains("failure ordering argument")
        ));
    }

    // --- Non-atomic function names ---

    #[test]
    fn non_atomic_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "std::vec::Vec::push",
                &ptr_val_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    #[test]
    fn empty_name_returns_none() {
        assert!(parse_atomic_intrinsic("", &[], &default_dest(), &default_span(),).is_none());
    }

    #[test]
    fn indirect_call_returns_none() {
        assert!(
            parse_atomic_intrinsic("<indirect>", &[], &default_dest(), &default_span(),).is_none()
        );
    }

    // --- Place extraction ---

    #[test]
    fn place_extracted_from_copy_arg() {
        let args = vec![Operand::Copy(Place { local: 5, projections: vec![Projection::Deref] })];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_seqcst",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place.local, 5);
        assert_eq!(op.place.projections, vec![Projection::Deref]);
    }

    #[test]
    fn place_extracted_from_move_arg() {
        let args = vec![Operand::Move(Place::local(7))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(7));
    }

    #[test]
    fn place_fallback_for_constant_arg() {
        let args = vec![Operand::Constant(ConstValue::Uint(0, 64))];
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &args,
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(0), "falls back to Place::local(0)");
    }

    #[test]
    fn place_fallback_for_no_args() {
        let op = parse_atomic_intrinsic(
            "core::intrinsics::atomic_load_relaxed",
            &[],
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.place, Place::local(0));
    }

    // --- Bare fence/compiler_fence paths ---

    #[test]
    fn bare_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::fence",
            &fence_order_args(AtomicOrdering::Acquire),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::Fence);
        assert_eq!(op.ordering, AtomicOrdering::Acquire);
    }

    #[test]
    fn bare_compiler_fence_path() {
        let op = parse_atomic_intrinsic(
            "std::sync::atomic::compiler_fence",
            &fence_order_args(AtomicOrdering::Release),
            &default_dest(),
            &default_span(),
        )
        .unwrap();
        assert_eq!(op.op_kind, AtomicOpKind::CompilerFence);
        assert_eq!(op.ordering, AtomicOrdering::Release);
    }

    #[test]
    fn bare_fence_missing_ordering_is_malformed() {
        let parsed = parse_atomic_intrinsic_metadata(
            "std::sync::atomic::fence",
            &[],
            &default_dest(),
            &default_span(),
        );
        assert!(matches!(
            parsed,
            AtomicIntrinsicMetadata::Malformed { detail }
                if detail.contains("fence ordering argument")
        ));
    }

    // --- All five orderings on a single operation ---

    #[test]
    fn all_orderings_for_xadd() {
        let orderings = [
            ("relaxed", AtomicOrdering::Relaxed),
            ("acquire", AtomicOrdering::Acquire),
            ("release", AtomicOrdering::Release),
            ("acqrel", AtomicOrdering::AcqRel),
            ("seqcst", AtomicOrdering::SeqCst),
        ];
        for (suffix, expected) in &orderings {
            let name = format!("core::intrinsics::atomic_xadd_{suffix}");
            let op =
                parse_atomic_intrinsic(&name, &ptr_val_args(), &default_dest(), &default_span())
                    .unwrap();
            assert_eq!(op.ordering, *expected, "xadd_{suffix} should be {expected:?}");
        }
    }

    // --- CAS ordering combinations ---

    #[test]
    fn cas_all_valid_combinations() {
        let cases = [
            ("seqcst_seqcst", AtomicOrdering::SeqCst, AtomicOrdering::SeqCst),
            ("seqcst_acquire", AtomicOrdering::SeqCst, AtomicOrdering::Acquire),
            ("seqcst_relaxed", AtomicOrdering::SeqCst, AtomicOrdering::Relaxed),
            ("acqrel_acquire", AtomicOrdering::AcqRel, AtomicOrdering::Acquire),
            ("acqrel_relaxed", AtomicOrdering::AcqRel, AtomicOrdering::Relaxed),
            ("acquire_acquire", AtomicOrdering::Acquire, AtomicOrdering::Acquire),
            ("acquire_relaxed", AtomicOrdering::Acquire, AtomicOrdering::Relaxed),
            ("release_relaxed", AtomicOrdering::Release, AtomicOrdering::Relaxed),
            ("relaxed_relaxed", AtomicOrdering::Relaxed, AtomicOrdering::Relaxed),
        ];
        for (suffix, exp_success, exp_failure) in &cases {
            let name = format!("core::intrinsics::atomic_cxchg_{suffix}");
            let op = parse_atomic_intrinsic(&name, &cas_args(), &default_dest(), &default_span())
                .unwrap();
            assert_eq!(op.ordering, *exp_success, "CAS {suffix} success");
            assert_eq!(op.failure_ordering, Some(*exp_failure), "CAS {suffix} failure");
        }
    }

    // --- Invalid ordering suffix returns None ---

    #[test]
    fn invalid_ordering_suffix_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "core::intrinsics::atomic_load_bogus",
                &ptr_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    #[test]
    fn invalid_cas_ordering_returns_none() {
        assert!(
            parse_atomic_intrinsic(
                "core::intrinsics::atomic_cxchg_seqcst_bogus",
                &cas_args(),
                &default_dest(),
                &default_span(),
            )
            .is_none()
        );
    }

    #[test]
    fn form_a_invalid_ordering_suffix_is_malformed_atomic_metadata() {
        assert_malformed_atomic_metadata(
            "core::intrinsics::atomic_load_bogus",
            &ptr_args(),
            "load_bogus",
        );
    }

    #[test]
    fn form_a_cas_missing_failure_ordering_is_malformed_atomic_metadata() {
        assert_malformed_atomic_metadata(
            "core::intrinsics::atomic_cxchg_seqcst",
            &cas_args(),
            "cxchg_seqcst",
        );
    }

    #[test]
    fn form_a_cas_extra_ordering_component_is_malformed_atomic_metadata() {
        assert_malformed_atomic_metadata(
            "core::intrinsics::atomic_cxchg_seqcst_acquire_relaxed",
            &cas_args(),
            "cxchg_seqcst_acquire_relaxed",
        );
    }

    #[test]
    fn unsupported_overflow_assert_does_not_become_custom() {
        let msg = mir::AssertKind::Overflow(mir::BinOp::Offset, local_operand(1), local_operand(2));
        let err = convert_assert_message(&msg).expect_err("Offset overflow is unsupported");
        assert!(
            err.contains("AssertKind::Overflow") && err.contains("BinOp::Offset"),
            "unsupported assert detail should be precise, got {err}",
        );
    }

    #[test]
    fn supported_overflow_assert_stays_structured() {
        let msg = mir::AssertKind::Overflow(mir::BinOp::Add, local_operand(1), local_operand(2));
        let converted = convert_assert_message(&msg).expect("Add overflow is modeled");
        assert!(matches!(converted, AssertMessage::Overflow(BinOp::Add)));
    }

    #[test]
    fn analysis_only_statements_lower_to_metadata_noops() {
        let statements = synthetic_statement_shapes();

        assert!(
            matches!(statements.get("fake_read"), Some(Statement::Nop)),
            "fake read is borrow-check metadata and must lower to Nop, got {:?}",
            statements.get("fake_read")
        );

        assert!(
            matches!(statements.get("ascribe_user_type"), Some(Statement::Nop)),
            "user type ascription is type-check metadata and must lower to Nop, got {:?}",
            statements.get("ascribe_user_type")
        );

        assert!(
            matches!(statements.get("backward_incompatible_drop_hint"), Some(Statement::Nop)),
            "backward-incompatible drop hint is lint metadata and must lower to Nop, got {:?}",
            statements.get("backward_incompatible_drop_hint")
        );
    }

    #[test]
    fn analysis_only_terminators_lower_to_runtime_gotos() {
        let terminators = synthetic_terminator_shapes();

        assert!(
            matches!(terminators.get("false_edge"), Some(Terminator::Goto(BlockId(7)))),
            "FalseEdge must lower to its real runtime target, got {:?}",
            terminators.get("false_edge")
        );

        assert!(
            matches!(terminators.get("false_unwind"), Some(Terminator::Goto(BlockId(11)))),
            "FalseUnwind must lower to its real runtime target, got {:?}",
            terminators.get("false_unwind")
        );

        assert!(
            matches!(terminators.get("coroutine_drop"), Some(Terminator::Return)),
            "CoroutineDrop is terminal coroutine drop-glue return, got {:?}",
            terminators.get("coroutine_drop")
        );

        assert!(
            matches!(terminators.get("unwind_resume"), Some(Terminator::Resume)),
            "UnwindResume must lower to a no-obligation Resume sink (not Opaque/Unreachable), got {:?}",
            terminators.get("unwind_resume")
        );

        assert!(
            matches!(
                terminators.get("unwind_terminate"),
                Some(Terminator::Opaque { kind, targets, .. })
                    if kind.contains("UnwindTerminate") && targets.is_empty()
            ),
            "UnwindTerminate must remain distinct and fail closed until TrustIr has an abort sink, got {:?}",
            terminators.get("unwind_terminate")
        );
    }

    #[test]
    fn direct_bit_intrinsic_marker_requires_tcx_intrinsic_identity() {
        let callees = fixture_direct_callees();
        for intrinsic in ["ctpop", "cttz", "ctlz", "bswap", "bitreverse"] {
            let compiler_key = format!("compiler_intrinsic_{intrinsic}");
            let compiler_intrinsic =
                callees.get(&compiler_key).expect("compiler intrinsic wrapper extracted");
            assert_eq!(compiler_intrinsic.len(), 1, "expected one direct {intrinsic} call");
            assert!(
                compiler_intrinsic[0].starts_with(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX),
                "TyCtxt-confirmed body-less {intrinsic} must carry the marker: {:?}",
                compiler_intrinsic
            );
            assert!(
                compiler_intrinsic[0].contains(&format!("intrinsics::{intrinsic}")),
                "the marker must preserve the diagnostic intrinsic path: {:?}",
                compiler_intrinsic
            );

            let source_key = format!("source_spelled_intrinsics_{intrinsic}");
            let source_spelled =
                callees.get(&source_key).expect("source-spelled wrapper extracted");
            assert_eq!(source_spelled.len(), 1, "expected one source-spelled {intrinsic} call");
            assert!(
                !source_spelled[0].starts_with(trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX),
                "an intrinsics::{intrinsic}-shaped source DefPath must remain unmarked: {:?}",
                source_spelled
            );
            assert!(
                source_spelled[0].ends_with(&format!("::intrinsics::{intrinsic}")),
                "negative control must retain its colliding textual suffix: {:?}",
                source_spelled
            );
        }
    }

    #[test]
    fn unwind_actions_are_faithfully_recorded_as_edges() {
        // Every `mir::UnwindAction` maps to the corresponding `UnwindEdge`. A
        // `Cleanup(bb)` preserves the block index so the verifier reaches the
        // cleanup block; the non-block actions become in-function exits with no
        // in-CFG successor (`cleanup_target() == None`).
        assert_eq!(convert_unwind_action(mir::UnwindAction::Unreachable), UnwindEdge::Unreachable);
        assert_eq!(convert_unwind_action(mir::UnwindAction::Continue), UnwindEdge::Continue);
        assert_eq!(
            convert_unwind_action(mir::UnwindAction::Terminate(
                mir::UnwindTerminateReason::InCleanup
            )),
            UnwindEdge::Terminate
        );
        assert_eq!(
            convert_unwind_action(mir::UnwindAction::Cleanup(mir::BasicBlock::from_usize(9))),
            UnwindEdge::Cleanup(BlockId(9))
        );
        // Only a `Cleanup` edge contributes a real in-CFG successor block.
        assert_eq!(
            convert_unwind_action(mir::UnwindAction::Cleanup(mir::BasicBlock::from_usize(9)))
                .cleanup_target(),
            Some(BlockId(9))
        );
        assert_eq!(convert_unwind_action(mir::UnwindAction::Continue).cleanup_target(), None);
    }

    #[test]
    fn assert_and_direct_call_continue_unwind_are_exempt_indirect_call_stays_closed() {
        // Pinned end to end at the terminator level.
        //
        // Neither the Assert arm nor the Call arm fail-closes on an unwind edge; the
        // Drop arm no longer does either. All three now RECORD the unwind edge
        // faithfully via `convert_unwind_action` (`unwind: UnwindEdge::Continue`
        // here):
        //   * an Assert's unwind edge is taken ONLY when the assert FAILS (exactly
        //     the panic the verifier proves unreachable), so it carries no native
        //     obligation — but a `Cleanup(bb)` edge still routes to a real cleanup
        //     block, so we record the edge to keep that block reachable;
        //   * a Call's unwind edge is taken ONLY if the CALLEE PANICS — a hazard
        //     already tracked SEPARATELY (the callee's own verification, or the
        //     bridge's `trust-absent-callee-assumption` may-panic obligation keyed on
        //     callee RESOLUTION) — and a `Cleanup(bb)` edge keeps the cleanup block
        //     reachable so its live-local drops are verified.
        // The Call structuring applies to DIRECT calls only; INDIRECT calls stay closed.
        let results = extract_test_results();
        let terminators = &results.terminators;

        // Assert{unwind: Continue} -> STRUCTURED Assert routed to its success
        // target (BlockId(5)) with the unwind edge RECORDED (UnwindEdge::Continue),
        // NOT an Opaque fail-close. This keeps arithmetic lowering: every overflow-
        // checked `a + b` is an Assert whose ordinary panic-propagation edge is
        // unwind=Continue.
        assert!(
            matches!(
                terminators.get("assert_continue"),
                Some(Terminator::Assert {
                    target: BlockId(5),
                    msg: AssertMessage::Overflow(BinOp::Add),
                    unwind: UnwindEdge::Continue,
                    ..
                })
            ),
            "Assert with unwind=Continue must lower to a structured Assert routed to its \
             success target with the unwind edge recorded (not an Opaque fail-close), got {:?}",
            terminators.get("assert_continue")
        );

        // DIRECT Call{unwind: Continue} (compiled `direct_call_add` -> `add_helper`)
        // -> STRUCTURED Call routed to its normal-return target, NOT an Opaque
        // fail-close. First confirm the fixture really exercises the Continue edge.
        assert_eq!(
            results.call_unwind_actions.get("direct_call_add").map(String::as_str),
            Some("Continue"),
            "fixture must exercise a Call with unwind=Continue; got {:?}",
            results.call_unwind_actions.get("direct_call_add")
        );
        assert!(
            matches!(
                terminators.get("direct_call_add"),
                Some(Terminator::Call { func, target: Some(_), unwind: UnwindEdge::Continue, .. })
                    if func.contains("add_helper")
            ),
            "a DIRECT call with unwind=Continue must lower to a structured Call routed to its \
             success target with the unwind edge recorded, not an Opaque fail-close, got {:?}",
            terminators.get("direct_call_add")
        );

        // INDIRECT Call{unwind: Continue} -> still Opaque/fail-closed. The exemption
        // does NOT open indirect calls: with the unwind fail-close gone the call now
        // falls to the indirect fail-close (`Call(indirect)`), staying Opaque.
        assert!(
            matches!(
                terminators.get("call_continue"),
                Some(Terminator::Opaque { kind, .. }) if kind.contains("Call(indirect)")
            ),
            "an INDIRECT call must remain a fail-closed Opaque terminator, got {:?}",
            terminators.get("call_continue")
        );
    }

    #[test]
    fn ref_borrow_kinds_do_not_collapse_to_mutability() {
        let rvalues = const_aggregate_return_shapes();

        assert!(
            matches!(
                rvalues.get("__synthetic_ref_shared"),
                Some(Rvalue::Ref { mutable: false, place }) if place.local == 1
            ),
            "shared references should remain immutable refs, got {:?}",
            rvalues.get("__synthetic_ref_shared")
        );

        assert!(
            matches!(
                rvalues.get("__synthetic_ref_mut_default"),
                Some(Rvalue::Ref { mutable: true, place }) if place.local == 1
            ),
            "default mutable references should remain mutable refs, got {:?}",
            rvalues.get("__synthetic_ref_mut_default")
        );

        // verifier-coverage: TwoPhaseBorrow and ClosureCapture mutable
        // borrows now lower to ordinary `&mut` refs (identical to Default), since
        // the borrow-checker timing/capture distinction is irrelevant to safety
        // obligations on the post-borrowck MIR we extract.
        for name in ["__synthetic_ref_mut_two_phase", "__synthetic_ref_mut_closure_capture"] {
            assert!(
                matches!(
                    rvalues.get(name),
                    Some(Rvalue::Ref { mutable: true, place }) if place.local == 1
                ),
                "{name} should lower to a mutable ref, got {:?}",
                rvalues.get(name)
            );
        }

        // Fake borrows remain unsupported — they are pure borrow-check artifacts
        // with no runtime reference semantics.
        for (name, expected_kind) in [
            ("__synthetic_ref_fake_shallow", "BorrowKind::Fake::Shallow"),
            ("__synthetic_ref_fake_deep", "BorrowKind::Fake::Deep"),
        ] {
            let Some(Rvalue::Unsupported { kind, detail, operands }) = rvalues.get(name) else {
                panic!("expected unsupported marker for {name}, got {:?}", rvalues.get(name));
            };
            assert_eq!(kind, expected_kind);
            assert!(detail.contains("borrow"), "detail should explain borrow semantics: {detail}");
            assert!(matches!(operands.as_slice(), [Operand::Copy(place)] if place.local == 1));
        }
    }

    // --- Optimized constant aggregate return shapes ---

    #[test]
    fn wrap_unsafe_binder_rvalue_preserves_unsupported_marker() {
        let rvalue = const_aggregate_return_shapes()
            .get("__synthetic_wrap_unsafe_binder")
            .expect("synthetic WrapUnsafeBinder result should be recorded");
        let Rvalue::Unsupported { kind, detail, operands } = rvalue else {
            panic!("expected unsupported WrapUnsafeBinder rvalue, got {rvalue:?}");
        };
        assert_eq!(kind, "Rvalue::WrapUnsafeBinder");
        assert!(
            detail.contains("unsafe binder") && detail.contains("i32"),
            "unsupported detail should describe binder type, got {detail}",
        );
        assert!(matches!(operands.as_slice(), [Operand::Copy(place)] if place.local == 1));
    }

    #[test]
    fn optimized_const_char_return_preserves_scalar_value() {
        let rvalue = const_aggregate_return_shapes().get("char_return").unwrap();
        let Rvalue::Use(operand) = rvalue else {
            panic!("expected scalar use rvalue, got {rvalue:?}");
        };
        assert_constant_uint_operand(operand, 'A' as u128, 32);
    }

    #[test]
    fn optimized_const_tuple_char_preserves_char_and_i32_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_char").unwrap();
        let Rvalue::Aggregate(AggregateKind::Tuple, operands) = rvalue else {
            panic!("expected tuple aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_uint_operand(&operands[0], 'A' as u128, 32);
        assert_constant_int_operand(&operands[1], 1);
    }

    #[test]
    fn optimized_const_unit_return_stays_unit() {
        let rvalue = const_aggregate_return_shapes().get("unit_return").unwrap();
        assert!(matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Unit))));
    }

    // a `&str` literal must lower to `ConstValue::Str` carrying its
    // exact UTF-8 bytes — not to the old fail-closed `Operand::Unsupported`
    // marker that blocked `Proved` for every function touching a string literal.
    #[test]
    fn optimized_const_str_literal_return_carries_utf8_bytes() {
        let rvalue = const_aggregate_return_shapes().get("str_literal_return").unwrap();
        let Rvalue::Use(Operand::Constant(ConstValue::Str { bytes })) = rvalue else {
            panic!("expected `&str` const use rvalue, got {rvalue:?}");
        };
        assert_eq!(bytes.as_slice(), b"trust_str_fixture");
    }

    // Trust: a `&str` return type must lower to a `&[u8]` fat pointer (Slice<u8>),
    // not the old `Unsupported` marker that forced a spurious UnsupportedMir
    // obligation on every trivially-safe string function. Slice<u8> shares str's
    // Sort::Int fallback and fat-pointer classification, so only the type-walk
    // obligation is removed — real per-statement safety VCs are untouched.
    #[test]
    fn str_return_type_lowers_to_byte_slice_fat_pointer() {
        let ty = fixture_return_types().get("str_literal_return").unwrap();
        assert_eq!(
            ty,
            &Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
            },
        );
    }

    // T7 (fmt-template bytes): a `&[u8; N]` reference constant — the
    // `format_args!` TEMPLATE every formatted `panic!` hands to
    // `Arguments::new` — must carry its exact (non-UTF-8!) bytes as
    // `ConstValue::Str`, not degrade to the content-free `OpaqueConst`, so
    // the trust-vcgen contract-panic matcher can decode the literal pieces.
    #[test]
    fn byte_array_ref_const_carries_exact_bytes() {
        let rvalue = const_aggregate_return_shapes().get("byte_array_ref_return").unwrap();
        let Rvalue::Use(Operand::Constant(ConstValue::Str { bytes })) = rvalue else {
            panic!("expected `&[u8; N]` const to lower to ConstValue::Str, got {rvalue:?}");
        };
        assert_eq!(bytes.as_slice(), b"\x07prefix \xc0\x00");
    }

    // A `&[&str; N]` PIECES array (this toolchain's `Arguments::new` format template) now
    // lowers to the concatenated-pieces `ConstValue::Str` (so the contract-panic matcher can see
    // a formatted panic's message). The bytes are the pieces run together ("pa" + "pb"). This is
    // still an OPAQUE `Str` to the bridge (same content-free symbol as `OpaqueConst`), so nothing
    // downstream content-asserts it — the change is purely message VISIBILITY.
    #[test]
    fn str_array_ref_const_extracts_concatenated_pieces() {
        let rvalue = const_aggregate_return_shapes().get("str_array_ref_return").unwrap();
        let Rvalue::Use(Operand::Constant(ConstValue::Str { bytes })) = rvalue else {
            panic!(
                "expected `&[&str; N]` pieces const to lower to ConstValue::Str, got {rvalue:?}"
            );
        };
        assert_eq!(bytes.as_slice(), b"papb");
    }

    // Trust: a nested `&&str` const — the one `x == "lit"` produces by auto-ref'ing
    // the string literal to a promoted const — must peel to the inner `&str`'s bytes
    // (valtree transparency across `&`) and reuse the injectively-named
    // `ConstValue::Str`, not the fail-closed `Unsupported` marker that wedged the
    // ubiquitous string-comparison path.
    #[test]
    fn double_ref_str_const_carries_inner_bytes() {
        let rvalue = const_aggregate_return_shapes().get("double_ref_str").unwrap();
        let Rvalue::Use(Operand::Constant(ConstValue::Str { bytes })) = rvalue else {
            panic!("expected nested `&&str` const to lower to ConstValue::Str, got {rvalue:?}");
        };
        assert_eq!(bytes.as_slice(), b"trust_double_ref");
    }

    // The production MIR representation preserves the authored callback as a
    // real zero-upvar closure aggregate with its exact identity.
    fn assert_non_capturing_closure_aggregate_preserves_identity() {
        let rvalue = closure_test_results()
            .aggregates
            .get("closure_map_sum")
            .expect("expected the authored closure aggregate in closure_map_sum's MIR");
        let Rvalue::Aggregate(AggregateKind::Closure { name, captures, .. }, operands) = rvalue
        else {
            panic!("expected a closure aggregate, got {rvalue:?}");
        };
        assert_eq!(name, "trust_mir_extract_closures::closure_map_sum::{closure#0}");
        assert!(captures.is_empty(), "the authored closure must have no upvars");
        assert!(operands.is_empty(), "the zero-upvar aggregate must carry no operands");
    }

    // The zero-sized Const conversion seam preserves the same exact callback
    // identity without changing downstream unit/opaque value semantics. The
    // fixture constructs this Const from the real aggregate's compiler-owned
    // DefId/args; production extraction retains the aggregate above.
    #[test]
    fn non_capturing_closure_const_preserves_identity() {
        assert_non_capturing_closure_aggregate_preserves_identity();
        let operands = closure_test_operands();
        let operand = operands
            .get("closure_map_sum")
            .expect("expected the test-only closure Const constructed from closure_map_sum");
        let Operand::Constant(ConstValue::CallableItem {
            def_path,
            kind: CallableKind::Closure,
            def_path_hash,
        }) = operand
        else {
            panic!("expected a closure callable item, got {operand:?}");
        };
        assert_eq!(def_path, "trust_mir_extract_closures::closure_map_sum::{closure#0}");
        let other = operands
            .get("closure_map_sum_other")
            .expect("expected the test-only closure Const constructed from closure_map_sum_other");
        let Operand::Constant(ConstValue::CallableItem {
            def_path: other_path,
            kind: CallableKind::Closure,
            def_path_hash: other_hash,
        }) = other
        else {
            panic!("expected another closure callable item, got {other:?}");
        };
        assert_eq!(other_path, "trust_mir_extract_closures::closure_map_sum_other::{closure#0}");
        assert_eq!(
            def_path_hash.stable_crate_id(),
            other_hash.stable_crate_id(),
            "both definitions are from the same crate instance"
        );
        assert_ne!(
            def_path_hash.local_hash(),
            other_hash.local_hash(),
            "distinct closure definitions must retain distinct local hashes"
        );
    }

    #[test]
    fn compiler_generated_capturing_closure_const_remains_unsupported() {
        let operand = closure_test_results()
            .capturing
            .get("closure_map_sum")
            .expect("optimized iterator MIR should retain a capturing adapter closure control");
        let Operand::Unsupported { kind, detail } = operand else {
            panic!("capturing closure must remain fail-closed, got {operand:?}");
        };
        assert_eq!(kind, "Const::Closure");
        assert!(
            detail.contains("capturing closure constant")
                && detail.contains("must be represented as an aggregate"),
            "unexpected capturing-closure diagnostic: {detail}"
        );
    }

    #[test]
    fn function_item_zst_const_operand_preserves_identity() {
        let call_args = zst_const_operand_call_args();

        let args =
            call_args.get("pass_function_item").expect("missing call args for pass_function_item");
        assert_eq!(args.len(), 1, "expected one call arg, got {args:?}");
        let Operand::Constant(ConstValue::CallableItem {
            def_path,
            kind: CallableKind::FnDef,
            def_path_hash,
        }) = &args[0]
        else {
            panic!("expected a function callable item, got {:?}", args[0]);
        };
        assert_eq!(def_path, "trust_mir_extract_zst_const_operands::helper_fn_item");
        let other = call_args
            .get("pass_function_item_other")
            .expect("missing call args for pass_function_item_other");
        assert_eq!(other.len(), 1, "expected one call arg, got {other:?}");
        let Operand::Constant(ConstValue::CallableItem {
            def_path: other_path,
            kind: CallableKind::FnDef,
            def_path_hash: other_hash,
        }) = &other[0]
        else {
            panic!("expected another function callable item, got {:?}", other[0]);
        };
        assert_eq!(other_path, "trust_mir_extract_zst_const_operands::helper_fn_item_other");
        assert_eq!(
            def_path_hash.stable_crate_id(),
            other_hash.stable_crate_id(),
            "both definitions are from the same crate instance"
        );
        assert_ne!(
            def_path_hash.local_hash(),
            other_hash.local_hash(),
            "distinct function definitions must retain distinct local hashes"
        );
    }

    #[test]
    fn singleton_zst_struct_const_operands_lower_to_unit() {
        let call_args = zst_const_operand_call_args();

        for name in ["pass_local_zst", "pass_other_zst"] {
            let args =
                call_args.get(name).unwrap_or_else(|| panic!("missing call args for {name}"));
            assert_eq!(args.len(), 1, "expected one call arg for {name}, got {args:?}");
            assert_unit_operand(&args[0]);
        }
    }

    #[test]
    fn multi_variant_zst_enum_const_operand_stays_opaque() {
        let call_args = zst_const_operand_call_args();

        let args = call_args.get("pass_enum_zst").expect("missing call args for pass_enum_zst");
        assert_eq!(args.len(), 1, "expected one call arg for pass_enum_zst, got {args:?}");
        assert!(
            matches!(args[0], Operand::Constant(ConstValue::OpaqueConst)),
            "a fieldless multi-variant enum must retain an unconstrained discriminant, got {:?}",
            args[0]
        );
    }

    #[test]
    fn optimized_const_tuple_preserves_unit_and_i32_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_unit_i32").unwrap();
        let Rvalue::Aggregate(AggregateKind::Tuple, operands) = rvalue else {
            panic!("expected tuple aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_unit_operand(&operands[0]);
        assert_constant_int_operand(&operands[1], 1);
    }

    #[test]
    fn optimized_const_empty_enum_a_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("empty_enum_a").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::EmptyEnum");
        assert_eq!(*variant, 0);
        assert!(operands.is_empty(), "fieldless enum variant should not carry payload fields");
    }

    #[test]
    fn optimized_const_empty_enum_b_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("empty_enum_b").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::EmptyEnum");
        assert_eq!(*variant, 1);
        assert!(operands.is_empty(), "fieldless enum variant should not carry payload fields");
    }

    #[test]
    fn optimized_const_option_none_preserves_variant_shape() {
        let rvalue = const_aggregate_return_shapes().get("option_none").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Option");
        assert_eq!(*variant, 0);
        assert!(operands.is_empty(), "Option::None should not carry payload fields");
    }

    #[test]
    fn optimized_const_option_some_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("option_some").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Option");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 1);
    }

    #[test]
    fn optimized_const_result_ok_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("result_ok").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Result");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 1);
    }

    #[test]
    fn optimized_const_result_err_preserves_payload() {
        let rvalue = const_aggregate_return_shapes().get("result_err").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::Result");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 1);
        assert_constant_int_operand(&operands[0], 2);
    }

    #[test]
    fn optimized_const_named_array_preserves_elements() {
        let rvalue = const_aggregate_return_shapes().get("array_from_named_const").unwrap();
        let Rvalue::Aggregate(AggregateKind::Array, operands) = rvalue else {
            panic!("expected array aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 4);
        assert_constant_int_operand(&operands[1], 5);
    }

    #[test]
    fn optimized_const_plain_struct_preserves_fields() {
        let rvalue = const_aggregate_return_shapes().get("plain_struct").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::PlainStruct");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 3);
        assert_constant_int_operand(&operands[1], 4);
    }

    #[test]
    fn optimized_const_tuple_struct_preserves_fields() {
        let rvalue = const_aggregate_return_shapes().get("tuple_struct").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::TupleStruct");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 7);
        assert_constant_int_operand(&operands[1], 8);
    }

    #[test]
    fn optimized_const_pair_enum_preserves_multi_field_payload() {
        let rvalue = const_aggregate_return_shapes().get("pair_enum").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::PairEnum");
        assert_eq!(*variant, 0);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 9);
        assert_constant_int_operand(&operands[1], 10);
    }

    #[test]
    fn optimized_const_tagged_pair_enum_preserves_nonzero_variant_payload() {
        let rvalue = const_aggregate_return_shapes().get("tagged_pair_enum").unwrap();
        let Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, operands) = rvalue else {
            panic!("expected ADT aggregate rvalue, got {rvalue:?}");
        };
        assert_adt_name(name, "::TaggedPairEnum");
        assert_eq!(*variant, 1);
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 11);
        assert_constant_int_operand(&operands[1], 12);
    }

    #[test]
    fn optimized_const_small_array_preserves_elements() {
        let rvalue = const_aggregate_return_shapes().get("small_array").unwrap();
        let Rvalue::Aggregate(AggregateKind::Array, operands) = rvalue else {
            panic!("expected array aggregate rvalue, got {rvalue:?}");
        };
        assert_eq!(operands.len(), 2);
        assert_constant_int_operand(&operands[0], 5);
        assert_constant_int_operand(&operands[1], 6);
    }

    #[test]
    fn ptr_to_ptr_cast_lowers_to_typed_cast_rvalue() {
        let rvalue = cast_test_rvalues().get("ptr_to_ptr").unwrap();
        let Rvalue::Cast(Operand::Copy(place), target_ty) = rvalue else {
            panic!("expected PtrToPtr cast rvalue, got {rvalue:?}");
        };
        assert_eq!(place.local, 1);
        assert!(matches!(
            target_ty,
            Ty::RawPtr {
                mutable: false,
                pointee
            } if pointee.as_ref() == &Ty::u32()
        ));
    }

    #[test]
    fn array_ref_to_slice_ref_pointer_coercion_keeps_typed_slice_cast() {
        let rvalue = cast_test_rvalues().get("array_ref_to_slice_ref").unwrap();
        let Rvalue::Cast(Operand::Copy(place), target_ty) = rvalue else {
            panic!("expected a precise array-to-slice cast, got {rvalue:?}");
        };
        assert_eq!(place.local, 1);
        assert_eq!(
            target_ty,
            &Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
            }
        );
    }

    #[test]
    fn array_raw_ptr_to_slice_raw_ptr_pointer_coercion_fails_closed() {
        let rvalue = cast_test_rvalues().get("array_raw_ptr_to_slice_raw_ptr").unwrap();
        let Rvalue::Unsupported { kind, detail, operands } = rvalue else {
            panic!("expected unsupported PointerCoercion::Unsize marker, got {rvalue:?}");
        };
        assert_eq!(kind, "CastKind::PointerCoercion::Unsize");
        assert!(
            detail.contains("metadata/provenance semantics") && detail.contains("from Implicit"),
            "raw pointer unsize diagnostic should explain metadata/provenance and source, got {detail}",
        );
        assert!(matches!(operands.as_slice(), [Operand::Copy(place)] if place.local == 1));
    }

    #[test]
    fn function_item_to_fn_pointer_reify_lowers_to_typed_cast_rvalue() {
        let rvalue = cast_test_rvalues().get("function_item_to_fn_pointer").unwrap();
        let Rvalue::Cast(
            Operand::Constant(ConstValue::CallableItem {
                def_path, kind: CallableKind::FnDef, ..
            }),
            target_ty,
        ) = rvalue
        else {
            panic!("expected ReifyFnPointer cast rvalue, got {rvalue:?}");
        };
        assert_eq!(def_path, "trust_mir_extract_casts::helper_fn_item");
        let Ty::FnPtr { sig } = target_ty else {
            panic!("expected ReifyFnPointer target to lower as FnPtr, got {target_ty:?}");
        };
        assert!(sig.params.is_empty(), "helper function pointer takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
    }

    #[test]
    fn closure_to_fn_pointer_reify_lowers_to_typed_cast_rvalue() {
        let rvalue = cast_test_rvalues().get("closure_to_fn_pointer").unwrap();
        let Rvalue::Cast(
            Operand::Constant(ConstValue::CallableItem {
                def_path,
                kind: CallableKind::Closure,
                ..
            }),
            target_ty,
        ) = rvalue
        else {
            panic!("expected ClosureFnPointer cast rvalue, got {rvalue:?}");
        };
        assert_eq!(def_path, "trust_mir_extract_casts::closure_to_fn_pointer::{closure#0}");
        let Ty::FnPtr { sig } = target_ty else {
            panic!("expected ClosureFnPointer target to lower as FnPtr, got {target_ty:?}");
        };
        assert_eq!(sig.params.as_slice(), &[Ty::i32()]);
        assert_eq!(*sig.ret, Ty::i32());
    }

    #[test]
    fn safe_fn_pointer_to_unsafe_fn_pointer_lowers_to_typed_cast_rvalue() {
        let rvalue = cast_test_rvalues().get("function_pointer_to_unsafe").unwrap();
        let Rvalue::Cast(Operand::Copy(place), target_ty) = rvalue else {
            panic!("expected UnsafeFnPointer cast rvalue, got {rvalue:?}");
        };
        assert_eq!(place.local, 1);
        let Ty::FnPtr { sig } = target_ty else {
            panic!("expected UnsafeFnPointer target to lower as FnPtr, got {target_ty:?}");
        };
        assert!(sig.params.is_empty(), "helper function pointer takes no arguments: {sig:?}");
        assert_eq!(*sig.ret, Ty::i32());
    }

    #[test]
    fn borrowck_only_pointer_coercions_lower_like_typed_pointer_casts() {
        for name in
            ["__synthetic_mut_to_const_pointer_coercion", "__synthetic_array_to_pointer_coercion"]
        {
            let rvalue = cast_test_rvalues().get(name).unwrap();
            let Rvalue::Cast(Operand::Copy(place), target_ty) = rvalue else {
                panic!("expected {name} to lower as typed pointer cast, got {rvalue:?}");
            };
            assert_eq!(place.local, 1);
            assert!(matches!(
                target_ty,
                Ty::RawPtr {
                    mutable: false,
                    pointee
                } if pointee.as_ref() == &Ty::u8()
            ));
        }
    }

    #[test]
    fn transmute_cast_preserves_fail_closed_marker() {
        let rvalue = cast_test_rvalues().get("transmute_u32_bytes").unwrap();
        let Rvalue::Unsupported { kind, detail, operands } = rvalue else {
            panic!("expected unsupported Transmute marker, got {rvalue:?}");
        };
        assert_eq!(kind, "CastKind::Transmute");
        assert!(
            detail.contains("layout compatibility")
                && detail.contains("validity-invariant proof")
                && detail.contains("value-preserving cast"),
            "transmute diagnostic must reject identity-cast semantics, got {detail}",
        );
        assert!(matches!(operands.as_slice(), [Operand::Copy(place)] if place.local == 1));
    }

    // ========================================================================
    // Trust (goal item 2c regression, fix commit 2238fbfa9f):
    // `discharge_provably_safe_pointer_asserts` must ELIDE the null/misalign
    // UB-checks on a deref of a *received safe box*, and KEEP them on a raw
    // pointer, a relabeled box, or a mixed-def box. Compiler-driven: rustc's
    // CheckAlignment/CheckNull passes (run_optimization_passes, first two passes,
    // NOT o1()-gated → fire at every mir-opt-level) INSERT the asserts, gated on
    // `sess.ub_checks()`; then extract_body (lib.rs:1685) calls
    // discharge_provably_safe_pointer_asserts, which rewrites each DISCHARGED
    // assert's terminator to `Goto` (convert.rs:3378-3382). We capture the
    // POST-DISCHARGE VerifiableFunction and count surviving `Terminator::Assert`s
    // at BOTH -Zmir-opt-level=1 (Transmute box-deref source shape) and =3
    // (bare-NonNull-temp Use shape) — see received_box_facts (convert.rs:2967).
    //
    // VACUITY GUARD: the asserts only exist when rustc inserts them, so the
    // harness forces `-Zub-checks=yes` (else `sess.ub_checks()` merely defaults
    // to debug_assertions and any future -C opt-level would silently zero every
    // count). `rx_raw_ptr` (KEPT both) is the canary: a 0/0 there means ub-checks
    // got turned off and the test is vacuous — it fails loudly.
    // ========================================================================

    const BOX_ASSERT_FIXTURE_PATH: &str = "box_asserts.rs";

    const BOX_ASSERT_SOURCE: &str = r#"
pub fn rx_box_clean(a: Box<u64>) -> u64 { *a }

pub enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn eval(&self) -> i64 {
        match self {
            Expr::Lit(v) => *v,
            Expr::Add(a, b) => a.eval() + b.eval(),
        }
    }
}

pub fn rx_box_relabel(a: Box<u8>) -> u128 {
    let c: Box<u128> = unsafe { core::mem::transmute(a) };
    *c
}

pub fn rx_raw_ptr(p: *const u128) -> u128 {
    unsafe { *p }
}

pub fn mixed_def(c: bool, p: *mut u128) -> u128 {
    let x = if c { Box::new(0u128) } else { unsafe { Box::from_raw(p) } };
    *x
}

pub fn recv_mixed(a: Box<u128>, p: *mut u128, c: bool) -> u128 {
    let b = if c { a } else { unsafe { Box::from_raw(p) } };
    *b
}
"#;

    struct InMemoryBoxAssertFileLoader;

    impl rustc_span::source_map::FileLoader for InMemoryBoxAssertFileLoader {
        fn file_exists(&self, path: &Path) -> bool {
            path == Path::new(BOX_ASSERT_FIXTURE_PATH)
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            if self.file_exists(path) {
                Ok(BOX_ASSERT_SOURCE.to_string())
            } else {
                Err(io::Error::other("unexpected box-assert fixture path"))
            }
        }

        fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
            Err(io::Error::other("binary reads are not supported in box-assert tests"))
        }

        fn current_directory(&self) -> io::Result<PathBuf> {
            std::env::current_dir()
        }
    }

    /// Captures the POST-DISCHARGE `VerifiableFunction` for every free fn AND
    /// inherent/assoc method. Iterates `hir_body_owners` (NOT `hir_free_items`,
    /// which would MISS the inherent `Expr::eval`), filters to `Fn`/`AssocFn`,
    /// and keys by extract_function's derived name (`opt_item_name` → "eval").
    struct BoxAssertCallbacks {
        functions: BTreeMap<String, VerifiableFunction>,
    }

    impl rustc_driver::Callbacks for BoxAssertCallbacks {
        fn config(&mut self, config: &mut Config) {
            config.file_loader = Some(Box::new(InMemoryBoxAssertFileLoader));
        }

        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            use rustc_hir::def::DefKind;
            tcx.sess.dcx().abort_if_errors();

            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                    continue;
                }
                // optimized_mir → run_optimization_passes → CheckAlignment +
                // CheckNull INSERT the asserts; crate::extract_function →
                // extract_body → discharge_provably_safe_pointer_asserts then
                // rewrites the discharged ones to `Goto`, so `vf` is post-discharge.
                let body = tcx.optimized_mir(def_id);
                let vf = crate::extract_function(tcx, body);
                self.functions.insert(vf.name.clone(), vf);
            }

            Compilation::Stop
        }
    }

    /// Compile the fixture at a PARAMETERIZED mir-opt-level with UB-checks forced
    /// ON, returning the post-discharge `VerifiableFunction`s by name.
    fn compile_box_assert_fixture(opt_level: usize) -> BTreeMap<String, VerifiableFunction> {
        let mut callbacks = BoxAssertCallbacks { functions: BTreeMap::new() };
        let mut args = vec![
            "rustc".to_string(),
            BOX_ASSERT_FIXTURE_PATH.to_string(),
            "--crate-name".to_string(),
            "trust_mir_extract_box_asserts".to_string(),
            "--crate-type=lib".to_string(),
            "--edition=2021".to_string(),
            format!("-Zmir-opt-level={opt_level}"),
            // Force `sess.ub_checks() == true` independent of -C opt-level so the
            // CheckAlignment/CheckNull passes insert the Mis/Null asserts. Without
            // this the test is vacuous (all counts 0). parse_opt_bool accepts "yes".
            "-Zub-checks=yes".to_string(),
            "-Zno-codegen".to_string(),
            // Trust is on-by-default in this rustc_private compiler; without this the
            // inner fixture compile is REFUTED (box/raw derefs) and aborts before we
            // count asserts. Disables ONLY the fixture-compile verifier (empirically
            // required — verified 6/6 pass with it, 6/6 fail without).
            "-Ztrust-verify=off".to_string(),
            // Defensive: silence the (non-firing) transmute lint; warnings never
            // abort (abort_if_errors only aborts on errors) so this is optional.
            "-Aunnecessary_transmutes".to_string(),
        ];
        args.push("--sysroot".to_string());
        args.push(compiler_sysroot());
        if let Ok(backend) = std::env::var("RUSTC_CODEGEN_BACKEND") {
            args.push(format!("-Zcodegen-backend={backend}"));
        }

        let result =
            rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
                rustc_driver::run_compiler(&args, &mut callbacks);
                Ok(())
            });
        assert!(
            result.is_ok(),
            "failed to compile box-assert fixture at -Zmir-opt-level={opt_level}"
        );

        callbacks.functions
    }

    /// Memoized per opt level — each `compile_box_assert_fixture` spins a full
    /// rustc_driver invocation.
    fn box_assert_fixture(opt_level: usize) -> &'static BTreeMap<String, VerifiableFunction> {
        static OPT1: OnceLock<BTreeMap<String, VerifiableFunction>> = OnceLock::new();
        static OPT3: OnceLock<BTreeMap<String, VerifiableFunction>> = OnceLock::new();
        match opt_level {
            1 => OPT1.get_or_init(|| compile_box_assert_fixture(1)),
            3 => OPT3.get_or_init(|| compile_box_assert_fixture(3)),
            n => panic!("unsupported box-assert opt level {n}"),
        }
    }

    /// `(misalign asserts surviving, null asserts surviving)` in `name`.
    /// Uses `matches!` because `AssertMessage` derives NO `PartialEq`
    /// (model.rs:5680 = Debug, Clone, Serialize, Deserialize only).
    fn box_assert_counts(
        functions: &BTreeMap<String, VerifiableFunction>,
        name: &str,
    ) -> (usize, usize) {
        let vf = functions
            .get(name)
            .unwrap_or_else(|| panic!("box-assert fixture fn `{name}` was not extracted"));
        let mut mis = 0usize;
        let mut null = 0usize;
        for block in &vf.body.blocks {
            match &block.terminator {
                Terminator::Assert { msg: AssertMessage::MisalignedPointerDereference, .. } => {
                    mis += 1;
                }
                Terminator::Assert { msg: AssertMessage::NullPointerDereference, .. } => {
                    null += 1;
                }
                _ => {}
            }
        }
        (mis, null)
    }

    /// Assert the post-discharge Mis/Null outcome for `name` at BOTH opt levels.
    /// `*_kept == true` ⇒ assert survived (>= 1); `false` ⇒ discharged (== 0).
    /// The per-level `@opt{opt}` message keeps a level-3-only regression (e.g. a
    /// future mir-opt deleting a KEPT assert) distinguishable from a level-1 one.
    fn check_box_assert_discharge(name: &str, mis_kept: bool, null_kept: bool) {
        for &opt in &[1usize, 3usize] {
            let (mis, null) = box_assert_counts(box_assert_fixture(opt), name);
            if mis_kept {
                assert!(mis >= 1, "{name}@opt{opt}: expected Misalign KEPT, got {mis}");
            } else {
                assert_eq!(mis, 0, "{name}@opt{opt}: expected Misalign DISCHARGED, got {mis}");
            }
            if null_kept {
                assert!(null >= 1, "{name}@opt{opt}: expected Null KEPT, got {null}");
            } else {
                assert_eq!(null, 0, "{name}@opt{opt}: expected Null DISCHARGED, got {null}");
            }
        }
    }

    #[test]
    fn box_assert_rx_box_clean_discharges_both() {
        // Deref of a cleanly received Box<u64>: both checks provably dead.
        check_box_assert_discharge("rx_box_clean", false, false);
    }

    #[test]
    fn box_assert_eval_discharges_both() {
        // a.eval() + b.eval() over &Box<Expr>: received-box derefs, both discharged.
        check_box_assert_discharge("eval", false, false);
    }

    #[test]
    fn box_assert_rx_box_relabel_keeps_mis_only() {
        // transmute Box<u8> -> Box<u128>: Null discharges across the relabel, but
        // Misalign is KEPT (a pointee-relabeling cast was crossed;
        // align_of::<u8>() < align_of::<u128>() = required).
        check_box_assert_discharge("rx_box_relabel", true, false);
    }

    #[test]
    fn box_assert_rx_raw_ptr_keeps_both() {
        // *(p: *const u128): no box provenance -> both KEPT. Also the ub-checks
        // canary: a 0/0 here means -Zub-checks got disabled and the test is vacuous.
        check_box_assert_discharge("rx_raw_ptr", true, true);
    }

    #[test]
    fn box_assert_mixed_def_keeps_both() {
        // x defined by BOTH Box::new (Assign) and Box::from_raw (Call terminator):
        // the new local_has_terminator_def mixed-def guard fail-closes -> both KEPT.
        check_box_assert_discharge("mixed_def", true, true);
    }

    #[test]
    fn box_assert_recv_mixed_keeps_both() {
        // b = received Box<u128> in one arm, Box::from_raw(p) in the other: the
        // primary adversary counterexample -> both KEPT.
        check_box_assert_discharge("recv_mixed", true, true);
    }
}

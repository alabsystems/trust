// trust-clean/trustir_fold_expr.rs — Trust: structural-fold lane, RUNGS C + D
// (+ the RUNG-E kernel section at the bottom: the `wrapAdequate`/
// `wrapAdequateD` launch-composition theorems and the TExpr-valued
// `CallE`/`callResultE` call-transport twin consumed by the G-family wrapper
// lane, `trustir_fold_wrap.rs` — see that module's doc for the rung-E
// recognizers and the design-§3.4 option (a)/(b) split).
//
// The MEMOIZED Expr folders (docs/design/2026-07-10-structural-fold-lane.md
// §5 Rungs C and D): the DEPTHLESS rows (`FVarSubst`, `LevelParamSubst`,
// `LevelParamSubstSlice` — rung C) and the DEPTH-THREADING rows
// (`Instantiator`, `MultiInstantiator`, `Lifter`, `Lowerer`, `Abstractor` —
// rung D) of clean-kernel `expr/subst.rs` — the Expr-SCALE rows of the
// structural-fold lane, certified as an SCC UNIT spanning the concrete
// memoized wrapper (+ at rung D the folder's `fold_binder_body_opt`
// save/inc/call/restore override — the SAME SCC, one joint certificate)
// + the GENERIC `ExprFolderOpt` default-dispatch bodies
// (`fold_expr_opt_inner{,_full}` / `_extensions` / `_zfc` /
// `fold_zfc_set_expr_opt`, dumped ONCE, polymorphically, and specialized here
// by folder-context callee resolution) + the pinned first-party rebuild idioms
// (`merge2/3/4`, `ek`/`Expr::from_kind`, `Expr::kind`, `FoldMemo::get/put`,
// `stack_safe`, `checked_add_u32`).
//
// RUNG-D DEBUTS (design §5 Rung D):
//
//   D1. DEPTH-KEY MEMO — the memo key generalizes from the literal `(expr, 0)`
//       pair to `(expr, self.<depth-field>)`: the wrapper's `FoldMemo::get`
//       third argument is a COPY of the folder's sole mutable u32 field, and
//       `FoldMemo::put`'s is the PRE-call copy of the same field (`let depth =
//       self.depth;` before `stack_safe` — pinned; a post-call read would be
//       a stale-depth channel and declines `fold_memo::key_mismatch`). The
//       `memoAdequate` machinery generalizes to `memoAdequateD`: the lookup
//       oracle becomes `lk : TExpr → Int → Lk` (keyed on BOTH node and depth)
//       and the oracle-soundness hypothesis quantifies over both — P-ADDR at
//       rung D covers the PAIR `(address, depth)` (subst.rs's own SOUNDNESS
//       argument: the fold result is a pure function of `(node, depth)` for a
//       fixed-state folder).
//   D2. THE (d+1) IH SLOT — `fold_binder_body_opt`'s model is
//       `λ e d. foldD … e (dsucc d)` (design §3.1): the recognizer pins the
//       exact save/`checked_add_u32(+1)`/call/restore MIR (any deviation is a
//       NAMED decline: `fold_memo::missing_restore` for an absent/wrong
//       restore, `fold_memo::impure_state` for any other depth-field write,
//       `binder_body_shape` for everything else), and a binder-position child
//       (`Lam/Pi/Let` body, `CubicalPathLam` body, `ZFCComprehension` pred,
//       zfc `Separation` pred / `Replacement` func — read off the REAL
//       dispatch dumps, never hardcoded) maps to the recursor IH APPLIED AT
//       `dsucc d`, all other children at `d`. `dsucc` is a ∀-QUANTIFIED SLOT
//       of the interpreter (like G and the leaves): the kernel theorems are
//       parametric in the successor; the recognizer pins the real increment
//       to `expr::checked_add_u32(d, 1, _)` whose own dumped body is the
//       two-arg forwarding to `core::num::<impl u32>::saturating_add` — so
//       the real `dsucc` is the U32-SATURATING successor, carried as premise
//       P-SAT-ADD below (std semantics; NOT modeled as unbounded `d+1`).
//   D3. SCC-UNIT CERTIFICATION — the folder's `fold_expr_opt` AND
//       `fold_binder_body_opt` are ONE mutual-recursion SCC (design §0): the
//       recognizer takes both bodies together and one joint certificate
//       covers both rows (the census counts both; the binder row's gate arm
//       re-runs the SCC recognition from its wrapper co-member — no post-hoc
//       composition, exactly the design's "no cycle member sees a co-member
//       in the registry" discipline).
//   D4. THE INLINE-HASHMAP MEMO IDIOM (`Abstractor`) — same discipline, the
//       memo inlined: key tuple `(expr as *const _ as usize, self.depth)`
//       built once pre-call, `HashMap::get(&key)` / hit → `cached.clone()`
//       returned WHOLE / miss → `stack_safe` + `insert(key, result.clone())`
//       with the evicted `Option` dropped UNREAD and the RESULT (not the
//       clone) returned. P-ADDR/P-CLONE positions identical to the FoldMemo
//       fingerprints; P-OPT-STD covers `HashMap::get/insert`.
//
// RUNG-D LEAF HONESTY (the §3.3 leaf-slot pin discipline, decided here):
//   Depth-reading leaves (`fold_bvar_opt` reading `self.start`/`self.depth`,
//   `Abstractor::fold_fvar_opt` reading `self.depth`) fill the depth-family
//   leaf slots `leaf* : Int → … → OptE` — the depth field is the SOLE mutable
//   folder field (enforced SCC-wide), so at leaf-call time it equals the walk
//   depth `d` and the leaf denotes a pure function of `(d, payload,
//   immutable folder state)`; the gate arm certifies each override STANDALONE
//   exactly as at rung C. An UNCERTIFIED leaf override keeps the whole SCC
//   (BOTH rows) honestly declined — the OPAQUE-TOTAL-SLOT alternative
//   (certify the fold parametrically in an unconstrained leaf) is REJECTED
//   here because a blocked leaf is not provably total to this pipeline, so
//   modeling it as a total function would claim more than the code exhibits.
//
//   LEAF-ASSERT-UNHOSTAGE UPDATE (2026-07-11):
//   `Instantiator::fold_bvar_opt` now certifies through the exact
//   ORDERING-DISPATCH OPAQUE-CHAIN lane. Admission is pinned to its exact
//   def-path, whole-body content hash, complete 10-block shape, immutable u32
//   comparison operands, real Ordering carrier/tags, and one exact
//   `(VcKind, Formula)` digest. The kernel witness binds cmp/lift_at/bvar
//   results universally and proves only the three arm transports; the Greater
//   arm's `idx - 1` VC is refuted after adding `idx > depth` only to that one
//   pinned VC. No generic cmp fact is injected. Therefore Abstractor + Lifter
//   + Instantiator SCCs certify. MultiInstantiator / Lowerer remain honest
//   `leaf_uncertified` hostages: the former's `depth + n` overflow is genuinely
//   satisfiable and the latter's debug-assert panic arm is live MIR.
//
// RUNG-C DEBUTS (design §5 Rung C):
//
//   1. `TExpr` AT EXPR SCALE — the ExprKind mirror registered from the dump's
//      OWN type info (25 real variants; the recognizer reads the variant
//      table, discriminants, and field types out of the dump — never assumes
//      tag == declaration index). ZFC NESTING DECISION (design §3.1, deferred
//      twice, resolved here): `ExprKind::ZFCSet(ZFCSetExpr)` is FLATTENED —
//      the 9 `ZFCSetExpr` variants become 9 direct `TExpr` constructors
//      (`zfcEmpty … zfcChoice`), so `TExpr` has 25 − 1 + 9 = 33 constructors
//      and stays a SINGLE (non-mutual) inductive. Soundness of the flattening:
//      every `ZFCSetExpr` value occurs in an `Expr` kind-tree ONLY under the
//      1-field `ZFCSet` wrapper, and all `ZFCSetExpr` children are themselves
//      `Arc<Expr>`, so `ZFCSet ∘ ZfcCtor ↦ zfcCtor` is injective on reachable
//      kind-trees and arm-exact: the real fold's composed
//      `fold_zfc_set_expr_opt → .map(ZFCSet) → .map(ek)` per-z-variant
//      semantics equals the flattened ctor's one-level merge/map model (the
//      per-arm walk verifies the composition site by site). The MUTUAL-block
//      alternative was validated against the kernel (see
//      `mutual_two_type_inductive_block_registers` in the tests — the kernel
//      accepts a 2-type mutual `add_inductive`), so flattening is a modeling
//      CHOICE (simpler recursor, one motive), not a workaround.
//   2. `OptE` VALUE DOMAIN — the fold-interpreter family gains
//      `Option<Expr>`-sorted results: `OptE = none | some (e : TExpr)` with
//      the sharing-preserving rebuild combinators `merge2E/merge3E/merge4E`
//      (any-changed → `some (mk (pick old new)…)`, all-unchanged → `none`) and
//      `map1E` mirroring `merge2/3/4` + the `Option::map` single-child arms.
//      KIND-TREE PROPERTY TIER: the model is the `ExprKind` KIND TREE —
//      `ExprMeta` is ERASED (`ek`/`Expr::from_kind` recompute a derived cache;
//      the certified agreement is on the kind component; meta is separately
//      exercised by the already-certified `ExprMeta` rows and tests). Stated
//      here once and carried by every certificate this module mints.
//   3. THE MEMO IDIOM + `memoAdequate` — the depthless `FoldMemo::get`-before /
//      `FoldMemo::put`-after peel with the SAME `(expr, 0u32)` key pair
//      (depth LITERALLY 0 in both calls — verified against the real MIR; the
//      depth-THREADING folders (`Instantiator` &c., memo key = a depth FIELD
//      read) decline by name `fold_memo::depth_key_unsupported` until rung D).
//      The kernel-checked side is the CONDITIONAL MEMO-ADEQUACY THEOREM
//      (design §2 structure 1) over an abstract lookup oracle:
//
//        memoAdequate : ∀ G leaf* (lk : TExpr → Lk),
//          (∀ e r, lk e = Lk.hit r → r = foldE G leaf* e) →   -- the oracle-
//          ∀ e, memoFoldE G leaf* lk e = foldE G leaf* e      -- soundness HYP
//
//      proven by `TExpr.rec` (33 minors, each a dependent `Lk.rec` case split
//      + `congrArg`/`Eq.trans` IH rewriting). The hypothesis is P-ADDR's
//      theorem-level residence: an UNDISCHARGED HYPOTHESIS of a theorem, not
//      an axiom (`axiom_deps` stays empty). Note `memoFoldE` consults the
//      oracle BEFORE the guard while the real wrapper guards first — under
//      the oracle-soundness hypothesis both orders equal `foldE` pointwise
//      (a guard-false hit returns `foldE e = none` anyway), so the theorem
//      covers the real consult order; the RECOGNIZER pins the real order
//      exactly (guard → get → inner → put). What justifies instantiating the
//      hypothesis for the real memo is recognizer-side and NAMED (P-ADDR
//      below): the walk verifies the memo is touched by EXACTLY one
//      get-before/put-after pair keyed by the SAME (param, 0) pair, that
//      `put`'s value argument IS the fold result and its return value the
//      function's return, and that no other folder-state mutation exists
//      (deviations → `fold_memo::impure_state` / `fold_memo::key_mismatch`).
//
// NAMED TRANSLATION PREMISES (design §2/§6; the trustir_adt MODEL-ONLY honesty
// tier — kernel-checked, self-contained, not grounder-connected):
//   * P-ACYC — a runtime `Expr` is a finite kind-tree/DAG (immutable, built
//     bottom-up, no `Weak`, no interior mutability, `#![forbid(unsafe_code)]`
//     in clean-kernel), so it denotes a `TExpr`. The dump type-graph gate
//     admits only direct `Arc<Expr>` recursive edges with an exact measured
//     complete Arc layout; every non-scalar payload has an exact whole-graph
//     fingerprint, so opaque/name-only containers and any Weak/Cell/
//     UnsafeCell/atomic/lock/mutable-alias drift decline. A source-policy
//     regression tripwire pins the unsafe-code prohibition and recursively
//     scans the complete Expr/Level plus Name-value defining sources.
//   * P-ARC-DEREF — `<Arc<T> as Deref>::deref` returns the pointee (pinned by
//     the `ptr → NonNull → pointer → RawPtr → ArcInner → data` field path in
//     the dump's own type info + the `&Arc<..>` / `&Expr` local type pins,
//     exactly rung A/B's pin).
//   * P-STACK — `stacker::maybe_grow(r, s, f) = f()`, f called exactly once
//     (rung B's premise; the trampoline + closure fingerprints re-used here).
//   * P-ADDR — the memo key `(expr as *const Expr as usize, depth)` (depth
//     literally 0 at rung C; the folder's depth FIELD at rung D) is injective
//     on `(node, depth)` pairs visited during one fold call (the `FoldMemo`
//     SOUNDNESS comment's own argument, subst.rs:39-47). A memory-model fact
//     outside both MIR syntax and Clean; carried as the `memoAdequate` /
//     `memoAdequateD` hypothesis' real-world justification. NOTE an
//     extraction-layer sub-premise folded in: the raw historical dump renders
//     the ptr→usize cast result as `ConstValue::OpaqueConst` with the
//     `AddressOf` operand adjacent but unconnected. The authenticated decoder
//     restores only the three exact u64 occurrences to
//     `OpaqueScalar { width: 64, signed: false }`. Thus "the opaque key
//     component IS the taken address" remains part of P-ADDR's text, pinned
//     against the canonical authenticated scalar form and
//     `FoldMemo::get/put`'s exact dumped shape (and the inline `Abstractor`
//     key-tuple construction at rung D).
//   * P-SAT-ADD (rung D) — `core::num::<impl u32>::saturating_add(a, b)`
//     computes the u32-saturating sum (std semantics; the callee is std and
//     not dumped). The pinned `expr::checked_add_u32` body is checked to be
//     EXACTLY the two-arg forwarding to it, so the real depth successor is
//     `d ↦ min(d+1, u32::MAX)`. The kernel witness keeps `dsucc`
//     ∀-QUANTIFIED, so no unbounded `d+1` claim is smuggled in; the
//     certificate text identifies the slot with the saturating successor
//     under this premise.
//   * P-CLONE — `Expr::clone` (Arc-clone children + `Copy` meta) and
//     `Option<Expr>::clone` / `Option<&T>::cloned` / `Arc::clone` are identity
//     on the modeled kind-tree. `Expr::clone`'s own dumped body IS
//     fingerprint-checked (kind-field passthrough via `ExprKind::clone` +
//     meta copy); `Option`'s std derive and `Arc::clone`'s pointee identity
//     are std-semantics premise text.
//   * P-CTOR-ZST — RETIRED at the extraction root. Zero-sized fn items and
//     upvar-free closures now carry `ConstValue::CallableItem` with the exact
//     def-path, callable kind, and both rustc `DefPathHash` components. All 30
//     occurrences (16 identities) are conjunctively pinned. Each of the 14
//     constructor closures additionally resolves to a same-path co-member
//     with an exact whole-function content hash before its exact arity/type/
//     control-flow/constructor routing is walked. `ExprKind::App` and all 15
//     `Arc::new` positions have separate exact fn-item identities. Historical
//     `Unit`, any path/kind/hash/body drift, or a same-shaped callback swap
//     declines. Capturing callbacks remain named aggregates whose captures
//     and constructor bodies are walked with the same strict final-output
//     discipline. This is executable evidence, not a translation premise.
//   * P-OPT-STD — `Option::<T>::map` / `Option::<T>::map_or_else` /
//     `Option::<&T>::cloned` / `HashMap::get/insert` (as consulted through
//     the memo erasure) carry their std semantics; all uses are inside the
//     pinned first-party bodies with type-pinned operands.
//
// LEAF-SLOT POLICY (design §3.1/§3.3): the registered interpreter `foldE` is
// LEAF-PARAMETRIC — `should_descend` (G) and the five leaf hooks
// (`fold_bvar/fvar/sort/const/lit_opt`) are ∀-quantified slots. Per folder the
// recognizer RESOLVES each slot: a trait DEFAULT resolves to `λ_. none` (the
// generic default's own dumped body is checked to be the literal `None`
// return), an OVERRIDE must itself be CERTIFIED (the caller re-runs the
// non-fold via-trustir lanes + the safety pillars on the override's dump —
// order-independent, mirroring rung B's wrapper arm). An uncertifiable
// override (e.g. `LevelParamSubst::fold_sort_opt`'s `Level::substitute_map`
// call, `fold_const_opt`'s `Iterator::collect`) keeps the row HONESTLY
// declined (`leaf_uncertified`) — the design's "hostage" rows.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name, TypeChecker,
};
use trust_types::{
    AggregateKind, BasicBlock, BlockId, CallableDefPathHash, CallableKind, ConstValue, Operand,
    Place, Projection, Rvalue, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use crate::trustir_anchor::{RefinementVerdict, cst, int_ty};
use crate::trustir_fold::DumpBodies;

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

fn l1() -> Level {
    Level::succ(Level::zero())
}

// ===========================================================================
// Pins — every def-path this recognizer resolves against (drift → decline)
// ===========================================================================

/// The clean-kernel trait whose default dispatch this lane certifies.
pub(crate) const TRAIT_PREFIX: &str = "expr::visitor::opt::ExprFolderOpt";
const GEN_SHOULD_DESCEND: &str = "expr::visitor::opt::ExprFolderOpt::should_descend";
const GEN_FOLD_EXPR_OPT: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt";
const GEN_FOLD_EXPR_OPT_INNER: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner";
const GEN_FOLD_EXPR_OPT_INNER_FULL: &str =
    "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full";
const GEN_FOLD_EXPR_OPT_EXTENSIONS: &str =
    "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions";
const GEN_FOLD_EXPR_OPT_ZFC: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc";
const GEN_FOLD_ZFC_SET_EXPR_OPT: &str = "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt";
const GEN_FOLD_BINDER_BODY_OPT: &str = "expr::visitor::opt::ExprFolderOpt::fold_binder_body_opt";

const EXPR_KIND_ACCESSOR: &str = "expr::Expr::kind";
const EK_FN: &str = "expr::kind::ek";
const EXPR_FROM_KIND: &str = "expr::Expr::from_kind";
pub(crate) const EXPR_CLONE: &str = "<expr::Expr as std::clone::Clone>::clone";
const MERGE2_FN: &str = "expr::visitor::opt::merge2";
const MERGE3_FN: &str = "expr::visitor::opt::merge3";
const MERGE4_FN: &str = "expr::visitor::opt::merge4";
const FOLDMEMO_GET: &str = "expr::subst::FoldMemo::get";
const FOLDMEMO_PUT: &str = "expr::subst::FoldMemo::put";
pub(crate) const FOLDMEMO_TY: &str = "expr::subst::FoldMemo";
const OPTION_MAP: &str = "std::option::Option::<T>::map";
const OPTION_MAP_OR_ELSE: &str = "std::option::Option::<T>::map_or_else";
const OPTION_CLONED: &str = "std::option::Option::<&T>::cloned";
const HASHMAP_GET: &str = "std::collections::HashMap::<K, V, S, A>::get";
const HASHMAP_INSERT: &str = "std::collections::HashMap::<K, V, S, A>::insert";
pub(crate) const CLONE_CLONE: &str = "std::clone::Clone::clone";
const ARC_DEREF: &str = "std::ops::Deref::deref";
/// Rung D: the depth-increment helper (its own dumped body is fingerprinted —
/// the P-SAT-ADD position) and the std callee it forwards to.
const CHECKED_ADD_U32: &str = "expr::checked_add_u32";
const SATURATING_ADD_U32: &str = "core::num::<impl u32>::saturating_add";
/// Rung D: the inline-memo (Abstractor) HashMap field type pin.
const HASHMAP_TY: &str = "std::collections::HashMap";
const FNONCE_CALL_ONCE: &str = "std::ops::FnOnce::call_once";
pub(crate) const TOTAL_CLONE: &str = "__trust_total_clone";
pub(crate) const EXPR_NAME: &str = "expr::Expr";
const EXPR_KIND_NAME: &str = "expr::kind::ExprKind";
const ZFC_SET_EXPR_NAME: &str = "expr::kind::ZFCSetExpr";
pub(crate) const OPTION_NAME: &str = "std::option::Option";

/// Exact callable identities emitted by the audited stage1 extractor build.
/// The path+kind identify callback semantics; both DefPathHash components pin
/// the extraction/build identity and make any crate-instance or local-def
/// drift explicit. Callback behavior is additionally checked from each
/// closure's co-member body below.
#[derive(Clone, Copy, PartialEq, Eq)]
struct CallablePin {
    path: &'static str,
    kind: CallableKind,
    hash: CallableDefPathHash,
    body_hash: Option<&'static str>,
}

const fn callable_pin(
    path: &'static str,
    kind: CallableKind,
    stable_crate_id: u64,
    local_hash: u64,
) -> CallablePin {
    CallablePin {
        path,
        kind,
        hash: CallableDefPathHash::new(stable_crate_id, local_hash),
        body_hash: None,
    }
}

const fn closure_pin(
    path: &'static str,
    stable_crate_id: u64,
    local_hash: u64,
    body_hash: &'static str,
) -> CallablePin {
    CallablePin {
        path,
        kind: CallableKind::Closure,
        hash: CallableDefPathHash::new(stable_crate_id, local_hash),
        body_hash: Some(body_hash),
    }
}

const LOCAL_CALLABLE_CRATE: u64 = 0x7508_ca85_e610_0c00;
const ARC_CALLABLE_CRATE: u64 = 0x9d72_b10b_1284_1225;
const ARC_NEW_CALLABLE: CallablePin = callable_pin(
    "std::sync::Arc::<T>::new",
    CallableKind::FnDef,
    ARC_CALLABLE_CRATE,
    0xe31a_916e_7093_729f,
);
const APP_CTOR_CALLABLE: CallablePin = callable_pin(
    "expr::kind::ExprKind::App",
    CallableKind::FnDef,
    LOCAL_CALLABLE_CRATE,
    0xbc8c_212d_f299_ed62,
);

const INNER_FULL_CLOSURE_5: CallablePin = closure_pin(
    "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full::{closure#5}",
    LOCAL_CALLABLE_CRATE,
    0x6b7b_4c5c_fd70_ffdd,
    "b331095a3a727ace9235cc5212be3940ae0d3f867077d4e8656904bc4aad78f6",
);
const EXTENSION_CLOSURES: [CallablePin; 6] = [
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#0}",
        LOCAL_CALLABLE_CRATE,
        0x5fdc_c319_17fb_4403,
        "cadac6b6f1303466d22529d2c63443b57606adcae2fdea48a95b2e9e970ffd04",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#1}",
        LOCAL_CALLABLE_CRATE,
        0xe564_c158_55b3_eedd,
        "c2694fbf36863dec2022e5cf7e4c57378698d5b9138a29d3f58590053c51c001",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#2}",
        LOCAL_CALLABLE_CRATE,
        0x6d64_4c3f_403b_a3dc,
        "70f1df0d0f7aac15a36d5597da9f60bac41f9a7ff95fc26b0bdbee56251d52a2",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#3}",
        LOCAL_CALLABLE_CRATE,
        0xf62e_e26e_807b_71f2,
        "b08f89bb120a64755aef6fc1aa89e61f47671f7d6ae473a5817f90d1a5b53c25",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#4}",
        LOCAL_CALLABLE_CRATE,
        0x57da_6213_2056_8a7c,
        "5fbdd97953675930e72f57a343a2cc051abfd391ede3d798ef65aea0b8c3f3b2",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#5}",
        LOCAL_CALLABLE_CRATE,
        0x73d8_d0b6_1d76_8ad6,
        "825f339ef2d305b30147b6eda666a45c3976ccfe167e0b14db618ea0b7236712",
    ),
];
const ZFC_CLOSURES: [CallablePin; 3] = [
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#0}",
        LOCAL_CALLABLE_CRATE,
        0x4de2_3e93_e741_05f5,
        "8897f37073ffa74c4f2d617ff82eccf57bef04fe5455fd3dd76a289b1e3fb411",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#1}",
        LOCAL_CALLABLE_CRATE,
        0xf455_6b7b_11df_89e4,
        "fdefa28216db730415139536f84a8e23b030d0bca8c89f669913df13fa5cf2c9",
    ),
    closure_pin(
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#2}",
        LOCAL_CALLABLE_CRATE,
        0xacc3_5f8a_a986_b6c6,
        "9e6d2ff4bbe388fde7c95a6ec565629efbb5862c11fa9968182ccf5a396e9fc1",
    ),
];
const ZFC_SET_CLOSURES: [(usize, CallablePin); 4] = [
    (
        1,
        closure_pin(
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#0}",
            LOCAL_CALLABLE_CRATE,
            0x249a_8070_7f2b_b911,
            "08c88099c46a7a6d28ea2b1c754415fecfbdb09762eb4af00e9b66a56178040a",
        ),
    ),
    (
        3,
        closure_pin(
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#3}",
            LOCAL_CALLABLE_CRATE,
            0x5cf8_6988_9fb2_5a13,
            "5264cc84b793060a7386453510338dd508157f0e66944adee554da694e227150",
        ),
    ),
    (
        4,
        closure_pin(
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#4}",
            LOCAL_CALLABLE_CRATE,
            0x8321_5fd4_b3fd_48f4,
            "a90669d59b46f70a5cab76e19d9ad1783566af78d311fb606e7ef25b56b6c42f",
        ),
    ),
    (
        8,
        closure_pin(
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#9}",
            LOCAL_CALLABLE_CRATE,
            0x568d_d947_806e_692e,
            "0dbd990ce9a09aa8f37e30f061666d90b9928ed77d59d093aa7dbf1c46cc9d1c",
        ),
    ),
];

// ===========================================================================
// Named declines
// ===========================================================================

/// Why the Expr-scale fold recognizer declined — every decline NAMED
/// (design §6), nothing outside the fragment silently accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprFoldDecline {
    /// Signature is not `fn(&mut Folder, &Expr) -> Option<Expr>`.
    SignatureUnsupported(String),
    /// The wrapper body is not the pinned guard/get/stack_safe/put shape.
    WrapperShape(String),
    /// The memo key's depth component is neither the literal 0 (rung C) nor a
    /// copy of the folder's own u32 depth field (rung D) — an unsupported
    /// memo-key shape.
    DepthKeyUnsupported(String),
    /// get/put key operands disagree (different expr operand, different depth
    /// literal), or `put`'s value argument is not the fold result, or the
    /// cache-hit path does not return the cached value whole.
    KeyMismatch(String),
    /// A folder field other than the memo is mutated / the memo is touched
    /// outside the exact get-before/put-after pair, anywhere in the SCC.
    ImpureState(String),
    /// A pinned co-member body (generic dispatch, merge*, ek, kind, memo
    /// get/put, defaults) is missing from the sibling dump map.
    MissingCoMember(String),
    /// A pinned co-member body drifts from its fingerprint.
    CoMemberDrift { member: String, detail: String },
    /// The dispatch's tag→variant map is not total/unique/TyCtxt-vetted.
    UnmappedSwitchTarget(String),
    /// An arm's recursive call argument is not a strict subterm (design §6).
    NonSubtermRecursiveArg(String),
    /// The same child is folded twice on one path.
    DuplicateRecursiveCall(String),
    /// An arm reads/branches on a payload outside the leaf-call / rebuild
    /// passthrough positions.
    PayloadMisuse(String),
    /// An arm's statement/terminator is outside the pinned vocabulary.
    ArmShape { variant: String, detail: String },
    /// The `stack_safe` trampoline/closure fingerprint drifts (P-STACK).
    StackSafeDrift(String),
    /// The folder overrides a dispatch-internal method (`fold_expr_opt_inner*`
    /// / `fold_binder_body_opt` / `fold_zfc_set_expr_opt`), so the generic
    /// pinned bodies do not describe this folder.
    DispatchOverridden(String),
    /// A leaf-slot override exists but is not certifiable by the non-fold
    /// lanes (+ safety pillars) — the honest "hostage" decline. Checked by
    /// the prove.rs gate arm (needs the lane disjunction), NOT by
    /// `sem_expr_fold_shape_of`.
    LeafUncertified(String),
    /// The recursor/memo-adequacy witness for an otherwise-recognized SCC did
    /// not pass the Clean kernel modulo-3 gate. Kept distinct from a leaf
    /// hostage so diagnostics never mislabel a kernel failure as missing
    /// compositional coverage.
    KernelWitnessRejected(String),
    /// The dump-visible Expr/ExprKind/ZFC payload graph no longer supports
    /// P-ACYC: a recursive Expr edge bypasses the pinned `Arc<Expr>` child
    /// form, or a Weak/interior-mutable/mutable-alias channel appears.
    AcyclicityPremiseDrift(String),
    /// Rung D: the folder's `fold_binder_body_opt` override lacks the restore
    /// write (or restores something other than the saved entry depth) — the
    /// design-§6 "missing depth restore" kill.
    MissingRestore(String),
    /// Rung D: the `fold_binder_body_opt` override deviates from the pinned
    /// save/`checked_add_u32(+1)`/call/restore shape in any other way.
    BinderBodyShape(String),
}

impl ExprFoldDecline {
    /// Stable snake_case decline name (design §6 kill table + rung-C memo
    /// names).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            ExprFoldDecline::SignatureUnsupported(_) => "signature_unsupported",
            ExprFoldDecline::WrapperShape(_) => "wrapper_shape",
            ExprFoldDecline::DepthKeyUnsupported(_) => "fold_memo::depth_key_unsupported",
            ExprFoldDecline::KeyMismatch(_) => "fold_memo::key_mismatch",
            ExprFoldDecline::ImpureState(_) => "fold_memo::impure_state",
            ExprFoldDecline::MissingCoMember(_) => "missing_co_member",
            ExprFoldDecline::CoMemberDrift { .. } => "co_member_drift",
            ExprFoldDecline::UnmappedSwitchTarget(_) => "unmapped_switch_target",
            ExprFoldDecline::NonSubtermRecursiveArg(_) => "non_subterm_recursive_arg",
            ExprFoldDecline::DuplicateRecursiveCall(_) => "duplicate_recursive_call",
            ExprFoldDecline::PayloadMisuse(_) => "payload_misuse",
            ExprFoldDecline::ArmShape { .. } => "arm_shape",
            ExprFoldDecline::StackSafeDrift(_) => "stack_safe_drift",
            ExprFoldDecline::DispatchOverridden(_) => "dispatch_overridden",
            ExprFoldDecline::LeafUncertified(_) => "leaf_uncertified",
            ExprFoldDecline::KernelWitnessRejected(_) => "kernel_witness_rejected",
            ExprFoldDecline::AcyclicityPremiseDrift(_) => "acyclicity_premise_drift",
            ExprFoldDecline::MissingRestore(_) => "fold_memo::missing_restore",
            ExprFoldDecline::BinderBodyShape(_) => "binder_body_shape",
        }
    }
}

type R<T> = Result<T, ExprFoldDecline>;

// ===========================================================================
// The recognized shape
// ===========================================================================

/// A `TExpr` constructor field's kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TField {
    /// Recursive child (`Arc<Expr>` in the real variant) — a `TExpr` argument
    /// with an IH slot.
    Rec,
    /// Non-recursive payload (index / id / Name / Level / BinderData / bool /
    /// …) — an opaque `Int` atom the theorems ∀-quantify.
    Payload,
}

/// The leaf slots, in interpreter-parameter order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LeafSlot {
    BVar,
    FVar,
    Sort,
    Const,
    Lit,
}

impl LeafSlot {
    fn method(self) -> &'static str {
        match self {
            LeafSlot::BVar => "fold_bvar_opt",
            LeafSlot::FVar => "fold_fvar_opt",
            LeafSlot::Sort => "fold_sort_opt",
            LeafSlot::Const => "fold_const_opt",
            LeafSlot::Lit => "fold_lit_opt",
        }
    }
    const ALL: [LeafSlot; 5] =
        [LeafSlot::BVar, LeafSlot::FVar, LeafSlot::Sort, LeafSlot::Const, LeafSlot::Lit];
}

/// One recognized arm of the dispatch — the recognizer-RECONSTRUCTED model
/// term shape (design §3.2 step 4: derived from the MIR, independently of the
/// Clean definition).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TArm {
    /// The arm calls the folder's resolved leaf hook with the variant's
    /// payload fields in order.
    Leaf(LeafSlot),
    /// The arm returns `None` (SProp / interval endpoints / zfcEmpty /
    /// zfcInfinity).
    NoneArm,
    /// Single folded child rebuilt through `Option::map` (Proj/MData/Squash/
    /// PathLam/zfc single-child ctors): `map1E ih (mk payloads…)`. `binder`:
    /// the child is folded through `fold_binder_body_opt` (rung D: the IH is
    /// taken at `dsucc d`; ignored by the depthless family, whose
    /// `fold_binder_body_opt` is the checked pure delegation).
    Map1 { child: usize, binder: bool },
    /// K folded children rebuilt through `merge2/3/4` (or the zfc inline
    /// merge): `mergeKE olds ihs (mk payloads…)`. `children` = the recursive
    /// field indices in old-argument order; `binders[i]` marks child `i` as a
    /// `fold_binder_body_opt` recursion (see `Map1::binder`).
    Merge { children: Vec<usize>, binders: Vec<bool> },
}

/// One `TExpr` constructor: mirrors a real `ExprKind` variant (or a flattened
/// `ZFCSetExpr` variant), fields in declaration order, arm reconstructed from
/// the walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TCtor {
    /// Clean constructor name fragment (sanitized variant name; zfc variants
    /// prefixed `Zfc`).
    pub name: String,
    /// The real `SwitchInt` tag (dump discriminant). For flattened zfc ctors
    /// this is the ZFCSetExpr discriminant (namespaced by `zfc: true`).
    pub tag: i128,
    /// Whether this ctor came from the flattened `ZFCSetExpr` dispatch.
    pub zfc: bool,
    /// Field kinds in declaration order.
    pub fields: Vec<TField>,
    /// The reconstructed arm.
    pub arm: TArm,
}

/// How a leaf slot resolves for the recognized folder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafResolution {
    /// No override — the trait default (`λ_. none`), its dumped body checked
    /// to be the literal `None` return.
    DefaultNone,
    /// Override at this def-path; the gate arm must certify it separately.
    Override(String),
}

/// Rung D: the depth-threading facts of a recognized folder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemExprFoldDepth {
    /// The folder field index holding the u32 depth (the SOLE mutable field).
    pub depth_field: usize,
    /// The folder's `fold_binder_body_opt` override def-path (the SCC
    /// co-member row this joint certificate also covers).
    pub binder_body: String,
    /// The memo idiom: `false` = `FoldMemo::get/put`, `true` = the inline
    /// `HashMap` memo (`Abstractor`).
    pub inline_memo: bool,
}

/// The recognized Expr-scale memoized fold (depthless at rung C,
/// depth-threading at rung D).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemExprFold {
    /// The folder type's def-path (e.g. `expr::subst::FVarSubst`).
    pub folder: String,
    /// The folder field index holding the memo (`FoldMemo` or the inline
    /// `HashMap`).
    pub memo_field: usize,
    /// `None` = depthless (rung C); `Some` = depth-threading (rung D).
    pub depth: Option<SemExprFoldDepth>,
    /// The resolved `should_descend` override def-path (the G slot's
    /// implementation; must be certified by the gate arm).
    pub should_descend: String,
    /// Per-slot leaf resolution.
    pub leaves: Vec<(LeafSlot, LeafResolution)>,
    /// The 33 reconstructed constructors (25 real − ZFCSet + 9 flattened zfc),
    /// in dispatch order (declaration order; zfc block after the real
    /// variants, in ZFCSetExpr declaration order).
    pub ctors: Vec<TCtor>,
}

// ===========================================================================
// Small MIR helpers
// ===========================================================================

pub(crate) fn block(body: &VerifiableBody, id: BlockId) -> Option<&BasicBlock> {
    body.blocks.iter().find(|b| b.id == id)
}

/// Statements with storage/coverage noise removed.
pub(crate) fn real_stmts(b: &BasicBlock) -> Vec<&Statement> {
    b.stmts
        .iter()
        .filter(|s| {
            !matches!(
                s,
                Statement::StorageLive(_)
                    | Statement::StorageDead(_)
                    | Statement::Nop
                    | Statement::Coverage
                    | Statement::ConstEvalCounter
                    | Statement::PlaceMention(_)
            )
        })
        .collect()
}

/// The set of DROP-FLAG locals of a body: locals whose every assignment is a
/// `const bool` and whose only non-assignment use is as a `SwitchInt`
/// selector. Their `const bool` writes are semantic noise on the happy path
/// (they only steer unwind/epilogue drops of already-moved values).
fn drop_flag_locals(body: &VerifiableBody) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    let mut const_bool_only: BTreeSet<usize> = BTreeSet::new();
    let mut disqualified: BTreeSet<usize> = BTreeSet::new();
    let check_op = |op: &Operand, disq: &mut BTreeSet<usize>, allow: Option<usize>| {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            if Some(p.local) != allow {
                disq.insert(p.local);
            }
        }
    };
    for b in &body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                if place.projections.is_empty()
                    && matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Bool(_))))
                {
                    const_bool_only.insert(place.local);
                    continue;
                }
                // Any other assignment to it disqualifies.
                disqualified.insert(place.local);
                // Any read inside another rvalue disqualifies.
                match rvalue {
                    Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                        check_op(op, &mut disqualified, None);
                    }
                    Rvalue::BinaryOp(_, a, c) | Rvalue::CheckedBinaryOp(_, a, c) => {
                        check_op(a, &mut disqualified, None);
                        check_op(c, &mut disqualified, None);
                    }
                    Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            check_op(op, &mut disqualified, None);
                        }
                    }
                    _ => {}
                }
            }
        }
        match &b.terminator {
            Terminator::Call { args, .. } => {
                for a in args {
                    check_op(a, &mut disqualified, None);
                }
            }
            Terminator::Assert { cond, .. } => check_op(cond, &mut disqualified, None),
            // SwitchInt selector use is ALLOWED (that is the drop-flag role).
            _ => {}
        }
    }
    const_bool_only.retain(|l| !disqualified.contains(l));
    const_bool_only
}

/// Whether `place` is bare local `l` (no projections).
pub(crate) fn is_local(place: &Place, l: usize) -> bool {
    place.local == l && place.projections.is_empty()
}

pub(crate) fn op_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// `Option<...>` whose payload names `inner` (by Adt name).
fn is_option_of(ty: &Ty, inner: &str) -> bool {
    let Ty::Adt { name, variants, .. } = ty else { return false };
    if name != OPTION_NAME {
        return false;
    }
    // Option's Some variant carries the payload as its single field.
    variants.iter().any(|v| {
        v.fields
            .iter()
            .any(|(_, fty)| matches!(fty, Ty::Adt { name, .. } | Ty::Datatype { name, .. } if name == inner))
    })
}

/// The literal-0 u32 depth constant.
fn is_zero_depth_const(op: &Operand) -> bool {
    matches!(op, Operand::Constant(ConstValue::Uint(0, _)))
        || matches!(op, Operand::Constant(ConstValue::Int(0)))
}

/// Exact extractor-carried identity for a zero-sized callable constant.
/// Historical `ConstValue::Unit` deliberately returns `None`: accepting it
/// would reopen the callback-substitution gap this schema addition closes.
fn callable_const(op: &Operand) -> Option<(&str, CallableKind, CallableDefPathHash)> {
    match op {
        Operand::Constant(ConstValue::CallableItem { def_path, kind, def_path_hash }) => {
            Some((def_path, *kind, *def_path_hash))
        }
        _ => None,
    }
}

fn callable_identity_matches(
    path: &str,
    kind: CallableKind,
    hash: CallableDefPathHash,
    expected: CallablePin,
) -> bool {
    path == expected.path && kind == expected.kind && hash == expected.hash
}

fn operand_matches_callable(op: &Operand, expected: CallablePin) -> bool {
    callable_const(op)
        .is_some_and(|(path, kind, hash)| callable_identity_matches(path, kind, hash, expected))
}

fn pinned_callable_body<'a>(bodies: &'a DumpBodies, pin: CallablePin) -> R<&'a VerifiableFunction> {
    let body = co_member(bodies, pin.path)?;
    let expected = pin.body_hash.ok_or_else(|| ExprFoldDecline::CoMemberDrift {
        member: pin.path.to_string(),
        detail: "callable has no body hash pin".to_string(),
    })?;
    let actual = body.content_hash();
    if actual != expected {
        return Err(ExprFoldDecline::CoMemberDrift {
            member: pin.path.to_string(),
            detail: format!("callable body hash {actual}, want {expected}"),
        });
    }
    Ok(body)
}

// ===========================================================================
// Dump type-info tables
// ===========================================================================

/// A variant read off the dump's own type info.
#[derive(Debug, Clone)]
pub struct DumpVariant {
    pub name: String,
    pub discriminant: i128,
    /// Field kinds in declaration order (Rec = Arc<Expr>-recursive).
    pub fields: Vec<TField>,
}

/// Classify one ExprKind/ZFCSetExpr field type: `Rec` iff it is
/// `Arc<..pointee Expr..>` through the pinned P-ARC-DEREF path.
fn classify_field(fty: &Ty) -> TField {
    if crate::trustir_fold::arc_pointee_ty(fty)
        .is_some_and(|p| crate::trustir_fold::ty_names_enum(p, EXPR_NAME))
    {
        TField::Rec
    } else {
        TField::Payload
    }
}

/// Extract the full `ExprKind` variant table from a type that names it (the
/// `&ExprKind` local's pointee in the generic dispatch bodies). Fail-closed
/// `None` if the table is absent/unexpanded.
fn expr_kind_table(ty: &Ty) -> Option<Vec<DumpVariant>> {
    let Ty::Adt { name, variants, .. } = ty else { return None };
    if name != EXPR_KIND_NAME || variants.is_empty() {
        return None;
    }
    Some(
        variants
            .iter()
            .map(|v| DumpVariant {
                name: v.name.clone(),
                discriminant: v.discriminant,
                fields: v.fields.iter().map(|(_, fty)| classify_field(fty)).collect(),
            })
            .collect(),
    )
}

/// Extract the `ZFCSetExpr` variant table (from `fold_zfc_set_expr_opt`'s
/// `&ZFCSetExpr` parameter).
fn zfc_table(ty: &Ty) -> Option<Vec<DumpVariant>> {
    let Ty::Adt { name, variants, .. } = ty else { return None };
    if name != ZFC_SET_EXPR_NAME || variants.is_empty() {
        return None;
    }
    Some(
        variants
            .iter()
            .map(|v| DumpVariant {
                name: v.name.clone(),
                discriminant: v.discriminant,
                fields: v.fields.iter().map(|(_, fty)| classify_field(fty)).collect(),
            })
            .collect(),
    )
}

fn p_acyc_suspicious_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    ["cell", "atomic", "mutex", "rwlock", "oncelock", "lazylock", "weak"]
        .iter()
        .any(|needle| lower.contains(needle))
}

/// SHA-256 fingerprints of every non-recursive, non-scalar payload type in
/// the measured ExprKind table. These pin the *entire extracted type graph*,
/// including the logical `LevelVec = SmallVec<[Level; 2]>` and
/// `MDataMap = Vec<(Name, MDataValue)>` container representations. This is
/// deliberately stricter than accepting a container def-path: extraction can
/// compact/erase generic arguments, so a name-only allowance could silently
/// admit `SmallVec<Cell<_>>`, `Vec<Weak<Expr>>`, or an unknown opaque datatype.
const P_ACYC_PINNED_PAYLOAD_TYPE_HASHES: &[&str] = &[
    // expr::types::FVarId
    "6e5a8a931bdb9119513e9acdbba88d19ca374bf26371d7ad969fbe0d22802539",
    // level::Level (by-name datatype reference)
    "140facced53789e57b92f2ae07a9f6ca939c220994e81c4f1a16564354706567",
    // name::Name
    "3eafea658961e0973a3e500342027e2504e2610b3eecdf8a0a4a109b3f2d394d",
    // LevelVec / smallvec::SmallVec
    "8edc9993c1f3ad6c015210bd79ee49d08ee7903402fd5a377ffd33c2365db592",
    // expr::types::BinderData
    "80ebd84f521150bd0ea492e97c40e704310e3ee28afae66aa9efb45fdd1753ef",
    // expr::types::Literal (by-name datatype reference)
    "bbe50737b1371182917d0bbf0c5c630a5c538a476930076010f59353d9fb15ce",
    // MDataMap / std::vec::Vec
    "a69cb84829a96accbf0b65475ca467745db2307088dca4d5e838ab1e267cfd3e",
    // expr::kind::ZFCSetExpr (separately validated from its expanded table)
    "a7124ca6e20e509d37074e62861fa4957567cdde3b1fccbfa32125fbb624f7ef",
];

/// Full extracted `std::sync::Arc<expr::Expr>` layout. Merely finding the
/// `ptr -> ... -> ArcInner::data` path is insufficient: an adversarial/drifted
/// Arc-shaped ADT could retain that path while adding a Weak/interior-mutable
/// side channel in another field.
const P_ACYC_EXPR_ARC_TYPE_HASHES: &[&str] = &[
    // ExprKind table: ArcInner::data is a by-name Expr back-reference.
    "4d1c4fa9ce0391c531a279d7d1a0b5d55436489525445b79fc351c262c6b9786",
    // ZFCSetExpr table: ArcInner::data expands Expr's two fields locally.
    "375a273ab89b0c245a9401fbff0e1f75f88cf5291ba71d1ae6247eac5cc4b7b2",
];

fn p_acyc_type_hash(ty: &Ty) -> Option<String> {
    serde_json::to_vec(ty).ok().map(|bytes| trust_types::stable_sha256_hex(&bytes))
}

fn p_acyc_pinned_payload_type(ty: &Ty) -> bool {
    p_acyc_type_hash(ty)
        .is_some_and(|hash| P_ACYC_PINNED_PAYLOAD_TYPE_HASHES.contains(&hash.as_str()))
}

/// Validate one non-recursive Expr payload. Exact measured payload type graphs
/// are admitted above; every unknown/opaque ADT fails closed. Arc is the sole
/// generic container inspected logically: its pointee must resolve through the
/// pinned representation, and an Expr pointee is legal only when the caller has
/// already recognized the whole field as the direct `Arc<Expr>` recursive edge.
fn check_p_acyc_payload(ty: &Ty, path: &str) -> R<()> {
    let bad = |detail: String| ExprFoldDecline::AcyclicityPremiseDrift(detail);
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => {
            return Ok(());
        }
        Ty::Ref { mutable: true, .. } | Ty::RawPtr { mutable: true, .. } => {
            return Err(bad(format!("{path}: mutable reference/raw-pointer channel")));
        }
        Ty::Ref { inner, .. } => return check_p_acyc_payload(inner, path),
        Ty::RawPtr { .. } => {
            return Err(bad(format!("{path}: raw-pointer channel")));
        }
        Ty::Adt { name, .. } if name == "std::sync::Arc" => {
            let pointee = crate::trustir_fold::arc_pointee_ty(ty).ok_or_else(|| {
                bad(format!("{path}: Arc payload does not match the pinned pointee layout"))
            })?;
            if !p_acyc_type_hash(ty)
                .is_some_and(|hash| P_ACYC_EXPR_ARC_TYPE_HASHES.contains(&hash.as_str()))
            {
                return Err(bad(format!("{path}: unpinned full Arc payload layout")));
            }
            return check_p_acyc_payload(pointee, &format!("{path}<Arc-pointee>"));
        }
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => {
            if name == EXPR_NAME {
                return Err(bad(format!("{path}: Expr recursion is not a direct Arc<Expr> child")));
            }
            if p_acyc_suspicious_name(name) {
                return Err(bad(format!("{path}: forbidden payload type {name}")));
            }
            if p_acyc_pinned_payload_type(ty) {
                return Ok(());
            }
            return Err(bad(format!("{path}: unpinned payload type {name}")));
        }
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            return check_p_acyc_payload(elem, path);
        }
        Ty::Tuple(fields) => {
            for (index, field) in fields.iter().enumerate() {
                check_p_acyc_payload(field, &format!("{path}.{index}"))?;
            }
            return Ok(());
        }
        Ty::Closure { .. }
        | Ty::FnDef { .. }
        | Ty::FnPtr { .. }
        | Ty::Dynamic { .. }
        | Ty::Coroutine { .. } => {
            return Err(bad(format!("{path}: callable/dynamic/coroutine payload channel")));
        }
        Ty::Unsupported { kind, detail } => {
            return Err(bad(format!("{path}: unsupported payload type {kind}: {detail}")));
        }
        _ => return Err(bad(format!("{path}: unknown payload type"))),
    }
}

fn check_p_acyc_variant_table(ty: &Ty, owner: &str) -> R<()> {
    let Ty::Adt { variants, .. } = ty else {
        return Err(ExprFoldDecline::AcyclicityPremiseDrift(format!(
            "{owner}: variant table is not an expanded ADT"
        )));
    };
    for variant in variants {
        for (field_name, field) in &variant.fields {
            // The only recursive edge admitted into the TExpr model.
            if crate::trustir_fold::arc_pointee_ty(field)
                .is_some_and(|pointee| crate::trustir_fold::ty_names_enum(pointee, EXPR_NAME))
            {
                if !p_acyc_type_hash(field)
                    .is_some_and(|hash| P_ACYC_EXPR_ARC_TYPE_HASHES.contains(&hash.as_str()))
                {
                    return Err(ExprFoldDecline::AcyclicityPremiseDrift(format!(
                        "{owner}::{}.{}: recursive Arc<Expr> full layout drift",
                        variant.name, field_name
                    )));
                }
                continue;
            }
            check_p_acyc_payload(field, &format!("{owner}::{}.{}", variant.name, field_name))?;
        }
    }
    Ok(())
}

// ===========================================================================
// Wrapper matcher — the concrete row `<F as ExprFolderOpt>::fold_expr_opt`
// ===========================================================================

/// Facts extracted from the memoized-wrapper row body.
struct WrapperFacts {
    folder: String,
    memo_field: usize,
    /// `Some(depth_field)` for the rung-D depth-key wrappers.
    depth_field: Option<usize>,
    /// The inline-HashMap memo idiom (Abstractor) instead of `FoldMemo`.
    inline: bool,
    closure_name: String,
    trampoline: String,
}

/// Match the memoized wrapper (see the module doc's shape): the shared
/// guard/none prologue, then the memo tail — `FoldMemo::get/put` (depthless
/// literal-0 key at rung C, depth-field key at rung D) or the inline
/// `HashMap` memo (rung D, Abstractor). Every deviation is a named decline;
/// the memo-discipline checks live here.
#[allow(clippy::too_many_lines)]
fn match_wrapper(func: &VerifiableFunction) -> R<WrapperFacts> {
    let body = &func.body;
    let ws = |d: &str| ExprFoldDecline::WrapperShape(d.to_string());

    // Signature: fn(&mut Folder, &Expr) -> Option<Expr>.
    if body.arg_count != 2 {
        return Err(ExprFoldDecline::SignatureUnsupported(format!(
            "arg_count {} (want 2)",
            body.arg_count
        )));
    }
    if !is_option_of(&body.return_ty, EXPR_NAME) {
        return Err(ExprFoldDecline::SignatureUnsupported(
            "return type is not Option<Expr>".to_string(),
        ));
    }
    let Some(Ty::Ref { mutable: true, inner: folder_ty }) = body.locals.get(1).map(|l| &l.ty)
    else {
        return Err(ExprFoldDecline::SignatureUnsupported(
            "param 1 is not &mut Folder".to_string(),
        ));
    };
    let Ty::Adt { name: folder, fields: folder_fields, .. } = folder_ty.as_ref() else {
        return Err(ExprFoldDecline::SignatureUnsupported("folder is not a struct".to_string()));
    };
    let param_is_expr_ref = matches!(body.locals.get(2).map(|l| &l.ty),
        Some(Ty::Ref { mutable: false, inner }) if crate::trustir_fold::ty_names_enum(inner, EXPR_NAME));
    if !param_is_expr_ref {
        return Err(ExprFoldDecline::SignatureUnsupported("param 2 is not &Expr".to_string()));
    }

    // GLOBAL PURITY SCAN (fold_memo::impure_state): the ONLY projected uses of
    // the folder local `_1` anywhere in the body must be the guard reborrow
    // `&(*_1)` and the two memo-field borrows the exact match below consumes;
    // no write ever targets `_1` or a projection of it.
    for b in &body.blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == 1 {
                        return Err(ExprFoldDecline::ImpureState(format!(
                            "write through the folder local: {place:?}"
                        )));
                    }
                    if let Rvalue::Ref { mutable: true, place: p } = rvalue {
                        // The only &mut borrow allowed is the put-site memo
                        // field borrow, matched exactly below; any OTHER &mut
                        // of _1 (or anything else) is checked there. Here we
                        // only forbid &mut of non-folder locals to keep the
                        // walk simple.
                        if p.local != 1 {
                            return Err(ExprFoldDecline::ImpureState(format!(
                                "mutable borrow of a non-folder local: {p:?}"
                            )));
                        }
                    }
                    // Rung D hardening: a `&raw mut` anywhere is a mutation
                    // channel outside the modeled idiom (the inline memo's
                    // key takes `&raw const` of the expr param only).
                    if let Rvalue::AddressOf(true, p) = rvalue {
                        return Err(ExprFoldDecline::ImpureState(format!(
                            "mutable raw borrow in the wrapper: {p:?}"
                        )));
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if place.local == 1 =>
                {
                    return Err(ExprFoldDecline::ImpureState(
                        "discriminant/deinit write on the folder".to_string(),
                    ));
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &b.terminator {
            if dest.local == 1 {
                return Err(ExprFoldDecline::ImpureState(
                    "call destination is the folder local".to_string(),
                ));
            }
        }
    }

    // bb0: `_g = &(*_1)` + Call should_descend(_g, _2).
    let b0 = block(body, BlockId(0)).ok_or_else(|| ws("no entry block"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: gplace,
            rvalue: Rvalue::Ref { mutable: false, place: gsrc },
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(ws("entry statements are not exactly the guard reborrow"));
    };
    if !(gsrc.local == 1 && gsrc.projections == vec![Projection::Deref])
        || !gplace.projections.is_empty()
    {
        return Err(ws("guard reborrow is not &(*_1)"));
    }
    let Terminator::Call { func: callee, args, dest: sd_dest, target: Some(t1), .. } =
        &b0.terminator
    else {
        return Err(ws("entry does not end in the guard call"));
    };
    if callee != GEN_SHOULD_DESCEND {
        return Err(ws(&format!("guard callee is {callee}, not should_descend")));
    }
    let ok_args = matches!(args.as_slice(), [a, b] if op_local(a) == Some(gplace.local) && op_local(b) == Some(2));
    if !ok_args || !sd_dest.projections.is_empty() {
        return Err(ws("guard call args are not (&*self, expr)"));
    }

    // bb1: bool switch on the guard: [(0, none_bb)] otherwise cont_bb.
    let b1 = block(body, *t1).ok_or_else(|| ws("missing guard-switch block"))?;
    if !real_stmts(b1).is_empty() {
        return Err(ws("statements in the guard-switch block"));
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b1.terminator else {
        return Err(ws("no guard switch"));
    };
    if op_local(discr) != Some(sd_dest.local) {
        return Err(ws("guard switch selector is not the guard result"));
    }
    let [(0, none_bb)] = targets.as_slice() else {
        return Err(ws("guard switch targets are not exactly [(0, none)]"));
    };
    let cont_bb = *otherwise;

    // none arm: `_0 = None; goto ret` (or Return directly).
    let nb = block(body, *none_bb).ok_or_else(|| ws("missing none arm"))?;
    let none_ok = match real_stmts(nb).as_slice() {
        [
            Statement::Assign {
                place,
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops),
                ..
            },
        ] => is_local(place, 0) && name == OPTION_NAME && ops.is_empty(),
        _ => false,
    };
    if !none_ok {
        return Err(ws("none arm does not build Option::None into _0"));
    }

    // cont: the memo-get block. Fork on its terminator callee:
    // `FoldMemo::get` (rung C/D `FoldMemo` idiom) vs `HashMap::get` (rung D
    // inline idiom, Abstractor).
    let cb = block(body, cont_bb).ok_or_else(|| ws("missing memo-get block"))?;
    let base_blocks: [usize; 4] = [BlockId(0).0, t1.0, none_bb.0, cont_bb.0];
    match &cb.terminator {
        Terminator::Call { func: c, .. } if c == FOLDMEMO_GET => {
            match_foldmemo_tail(body, folder, folder_fields, nb, cb, &base_blocks)
        }
        Terminator::Call { func: c, .. } if c == HASHMAP_GET => {
            match_inline_tail(body, folder, folder_fields, nb, cb, &base_blocks)
        }
        _ => Err(ws("memo-get block does not call FoldMemo::get or HashMap::get")),
    }
}

/// The `FoldMemo::get/put` tail of the wrapper: literal-0 key (rung C) or
/// depth-field key (rung D).
#[allow(clippy::too_many_lines)]
fn match_foldmemo_tail(
    body: &VerifiableBody,
    folder: &str,
    folder_fields: &[(String, Ty)],
    nb: &BasicBlock,
    cb: &BasicBlock,
    base_blocks: &[usize],
) -> R<WrapperFacts> {
    let ws = |d: &str| ExprFoldDecline::WrapperShape(d.to_string());
    let cstmts = real_stmts(cb);
    // Exactly one shared memo-field borrow + AT MOST one folder-field COPY
    // (the rung-D depth key; consumed below — an unconsumed copy declines).
    let mut memo_borrow: Option<(&Place, &Place)> = None;
    let mut depth_copy: Option<(usize, usize)> = None; // (local, field)
    for st in &cstmts {
        match st {
            Statement::Assign {
                place, rvalue: Rvalue::Ref { mutable: false, place: src }, ..
            } => {
                if memo_borrow.replace((place, src)).is_some() {
                    return Err(ws("two borrows in the memo-get block"));
                }
            }
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } if place.projections.is_empty() && src.local == 1 => {
                let [Projection::Deref, Projection::Field(f)] = src.projections.as_slice() else {
                    return Err(ws(&format!("unmodeled memo-get folder read {src:?}")));
                };
                if depth_copy.replace((place.local, *f)).is_some() {
                    return Err(ws("two folder-field copies in the memo-get block"));
                }
            }
            other => {
                return Err(ws(&format!("unmodeled memo-get statement {other:?}")));
            }
        }
    }
    let Some((mplace, msrc)) = memo_borrow else {
        return Err(ws("memo-get block has no memo borrow"));
    };
    let memo_field = match msrc.projections.as_slice() {
        [Projection::Deref, Projection::Field(f)] if msrc.local == 1 => *f,
        _ => {
            return Err(ExprFoldDecline::ImpureState(format!(
                "memo borrow is not a folder field: {msrc:?}"
            )));
        }
    };
    // The borrowed field's declared type must be the pinned FoldMemo.
    let memo_ty_ok = folder_fields
        .get(memo_field)
        .is_some_and(|(_, fty)| matches!(fty, Ty::Adt { name, .. } if name == FOLDMEMO_TY));
    if !memo_ty_ok {
        return Err(ExprFoldDecline::ImpureState(format!(
            "folder field {memo_field} is not the pinned {FOLDMEMO_TY}"
        )));
    }
    let Terminator::Call { func: gcallee, args: gargs, dest: get_dest, target: Some(t2), .. } =
        &cb.terminator
    else {
        return Err(ws("no memo-get call"));
    };
    debug_assert_eq!(gcallee, FOLDMEMO_GET);
    let [gm, gk, gd] = gargs.as_slice() else {
        return Err(ws("memo-get arity"));
    };
    if op_local(gm) != Some(mplace.local) {
        return Err(ws("memo-get receiver is not the memo borrow"));
    }
    if op_local(gk) != Some(2) {
        return Err(ExprFoldDecline::KeyMismatch(
            "memo-get key is not the folded parameter".to_string(),
        ));
    }
    // The depth key component: literal 0 (rung C) or the folder's u32 depth
    // field copy (rung D). Anything else is an unsupported key shape.
    let depth_field: Option<usize> = if is_zero_depth_const(gd) {
        if depth_copy.is_some() {
            return Err(ws("unconsumed folder-field copy in the memo-get block"));
        }
        None
    } else if let Some((dl, df)) = depth_copy {
        if op_local(gd) != Some(dl) {
            return Err(ExprFoldDecline::DepthKeyUnsupported(format!(
                "memo-get depth operand {gd:?} is neither the literal 0 nor the folder depth-field copy"
            )));
        }
        if df == memo_field {
            return Err(ExprFoldDecline::KeyMismatch(
                "memo key field collides with the memo field".to_string(),
            ));
        }
        let depth_ty_ok = folder_fields
            .get(df)
            .is_some_and(|(_, fty)| matches!(fty, Ty::Int { width: 32, signed: false }));
        if !depth_ty_ok {
            return Err(ExprFoldDecline::DepthKeyUnsupported(format!(
                "memo key folder field {df} is not a u32 depth field"
            )));
        }
        Some(df)
    } else {
        return Err(ExprFoldDecline::DepthKeyUnsupported(format!(
            "memo-get depth operand {gd:?} is not the literal 0"
        )));
    };

    // hit switch: `_d = discr(_c)` + switch [(1,hit),(0,miss)] otherwise unreachable.
    let hb = block(body, *t2).ok_or_else(|| ws("missing hit-switch block"))?;
    let hstmts = real_stmts(hb);
    let [Statement::Assign { place: dplace, rvalue: Rvalue::Discriminant(dsrc), .. }] =
        hstmts.as_slice()
    else {
        return Err(ws("hit-switch block is not exactly the discriminant read"));
    };
    if !is_local(dsrc, get_dest.local) || !dplace.projections.is_empty() {
        return Err(ws("hit discriminant is not of the memo-get result"));
    }
    let Terminator::SwitchInt {
        discr: hdiscr,
        targets: htargets,
        otherwise: hother,
        exhaustive_enum_unreachable,
        ..
    } = &hb.terminator
    else {
        return Err(ws("no hit switch"));
    };
    if op_local(hdiscr) != Some(dplace.local) || !exhaustive_enum_unreachable {
        return Err(ws("hit switch is not the vetted Option discriminant switch"));
    }
    let (hit_bb, miss_bb) = match htargets.as_slice() {
        [(1, h), (0, m)] | [(0, m), (1, h)] => (*h, *m),
        _ => return Err(ws("hit switch targets are not the Option tags")),
    };
    let ob = block(body, *hother).ok_or_else(|| ws("missing hit otherwise"))?;
    if !matches!(ob.terminator, Terminator::Unreachable) {
        return Err(ws("hit otherwise is reachable"));
    }

    // hit arm: `_h = mv _c@V1.f0; _0 = mv _h; goto ret` — the cached value
    // returned WHOLE (any projection into it → partial cached use → decline).
    let hitb = block(body, hit_bb).ok_or_else(|| ws("missing hit arm"))?;
    let hit_ok = match real_stmts(hitb).as_slice() {
        [
            Statement::Assign {
                place: p1,
                rvalue: Rvalue::Use(Operand::Move(src) | Operand::Copy(src)),
                ..
            },
            Statement::Assign {
                place: p2,
                rvalue: Rvalue::Use(Operand::Move(mid) | Operand::Copy(mid)),
                ..
            },
        ] => {
            p1.projections.is_empty()
                && src.local == get_dest.local
                && src.projections == vec![Projection::Downcast(1), Projection::Field(0)]
                && is_local(p2, 0)
                && is_local(mid, p1.local)
        }
        _ => false,
    };
    if !hit_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "cache-hit path does not return the cached value whole".to_string(),
        ));
    }

    // miss arm: (rung D: the PRE-call depth copy, same field, FIRST) +
    // closure aggregate capturing exactly (_1, _2) + stack_safe call.
    let mb = block(body, miss_bb).ok_or_else(|| ws("missing miss arm"))?;
    let mstmts = real_stmts(mb);
    let (pre_copy_local, cl_stmt): (Option<usize>, &Statement) = match depth_field {
        None => {
            let [only] = mstmts.as_slice() else {
                return Err(ws("miss arm is not exactly the closure aggregate"));
            };
            (None, *only)
        }
        Some(df) => {
            let [pre, cl] = mstmts.as_slice() else {
                return Err(ws(
                    "depth-key miss arm is not exactly the pre-call depth copy + closure aggregate",
                ));
            };
            let Statement::Assign {
                place: pp,
                rvalue: Rvalue::Use(Operand::Copy(psrc) | Operand::Move(psrc)),
                ..
            } = pre
            else {
                return Err(ws("depth-key miss arm does not start with the depth copy"));
            };
            let pre_ok = pp.projections.is_empty()
                && psrc.local == 1
                && psrc.projections == vec![Projection::Deref, Projection::Field(df)];
            if !pre_ok {
                return Err(ExprFoldDecline::KeyMismatch(format!(
                    "pre-call depth copy reads {psrc:?}, not the memo key field {df}"
                )));
            }
            (Some(pp.local), *cl)
        }
    };
    let Statement::Assign {
        place: clplace,
        rvalue: Rvalue::Aggregate(AggregateKind::Closure { name: closure_name, .. }, cl_ops),
        ..
    } = cl_stmt
    else {
        return Err(ws("miss arm has no closure aggregate"));
    };
    let caps_ok =
        matches!(cl_ops.as_slice(), [a, b] if op_local(a) == Some(1) && op_local(b) == Some(2));
    if !caps_ok {
        return Err(ExprFoldDecline::StackSafeDrift(
            "delegation closure does not capture exactly (folder, expr)".to_string(),
        ));
    }
    let Terminator::Call { func: sscallee, args: ssargs, dest: ss_dest, target: Some(t3), .. } =
        &mb.terminator
    else {
        return Err(ws("no stack_safe call"));
    };
    let ss_args_ok = matches!(ssargs.as_slice(), [a] if op_local(a) == Some(clplace.local));
    if !ss_args_ok || !ss_dest.projections.is_empty() {
        return Err(ExprFoldDecline::StackSafeDrift(
            "trampoline argument is not the delegation closure".to_string(),
        ));
    }
    // The trampoline callee's own body is fingerprinted by the caller (it
    // needs the sibling map); record its def-path.
    let trampoline = sscallee.clone();

    // put block: `_pm = &mut (*_1).fK` + Call FoldMemo::put(_pm, _2, <depth>, _r) → _0.
    let pb = block(body, *t3).ok_or_else(|| ws("missing put block"))?;
    let pstmts = real_stmts(pb);
    let [
        Statement::Assign {
            place: pmplace,
            rvalue: Rvalue::Ref { mutable: true, place: pmsrc },
            ..
        },
    ] = pstmts.as_slice()
    else {
        return Err(ws("put block statements are not exactly the memo &mut borrow"));
    };
    let put_field = match pmsrc.projections.as_slice() {
        [Projection::Deref, Projection::Field(f)] if pmsrc.local == 1 => *f,
        _ => {
            return Err(ExprFoldDecline::ImpureState(format!(
                "put borrow is not a folder field: {pmsrc:?}"
            )));
        }
    };
    if put_field != memo_field {
        return Err(ExprFoldDecline::KeyMismatch(format!(
            "get uses folder field {memo_field} but put uses {put_field}"
        )));
    }
    let Terminator::Call { func: pcallee, args: pargs, dest: put_dest, target: Some(t4), .. } =
        &pb.terminator
    else {
        return Err(ws("no memo-put call"));
    };
    if pcallee != FOLDMEMO_PUT {
        return Err(ws(&format!("memo-put callee is {pcallee}")));
    }
    let [pm, pk, pd, pv] = pargs.as_slice() else {
        return Err(ws("memo-put arity"));
    };
    if op_local(pm) != Some(pmplace.local) {
        return Err(ws("memo-put receiver is not the memo borrow"));
    }
    if op_local(pk) != Some(2) {
        return Err(ExprFoldDecline::KeyMismatch(
            "memo-put key is not the folded parameter (get/put key drift)".to_string(),
        ));
    }
    match (depth_field, pre_copy_local) {
        (None, _) => {
            if !is_zero_depth_const(pd) {
                return Err(ExprFoldDecline::KeyMismatch(
                    "memo-put depth is not the same literal 0 as the get".to_string(),
                ));
            }
        }
        (Some(_), Some(pl)) => {
            // The put depth must be the PRE-call copy — a re-read after the
            // inner call would be a stale-depth channel; declined even
            // though the restore discipline would make it equal.
            if op_local(pd) != Some(pl) {
                return Err(ExprFoldDecline::KeyMismatch(
                    "memo-put depth is not the pre-call depth copy (stale-depth channel)"
                        .to_string(),
                ));
            }
        }
        (Some(_), None) => unreachable!("depth key implies a pre-call copy"),
    }
    if op_local(pv) != Some(ss_dest.local) {
        return Err(ExprFoldDecline::KeyMismatch(
            "memo-put value is not the fold result (put of a non-result value)".to_string(),
        ));
    }
    if !is_local(put_dest, 0) {
        return Err(ExprFoldDecline::KeyMismatch(
            "memo-put result is not the function return".to_string(),
        ));
    }

    // Return block.
    let rb = block(body, *t4).ok_or_else(|| ws("missing return block"))?;
    if !matches!(rb.terminator, Terminator::Return) || !real_stmts(rb).is_empty() {
        return Err(ws("put does not flow directly to Return"));
    }
    // The none arm must also flow to a Return (directly or via this block).
    match &nb.terminator {
        Terminator::Return => {}
        Terminator::Goto(g) if *g == *t4 => {}
        _ => return Err(ws("none arm does not flow to Return")),
    }

    // Account for every block. Any EXTRA block is unaccounted behavior →
    // decline.
    let mut matched: std::collections::BTreeSet<usize> = base_blocks.iter().copied().collect();
    matched.extend([t2.0, hother.0, hit_bb.0, miss_bb.0, t3.0, t4.0]);
    if body.blocks.iter().any(|b| !matched.contains(&b.id.0)) {
        return Err(ws("wrapper has unaccounted blocks"));
    }

    Ok(WrapperFacts {
        folder: folder.to_string(),
        memo_field,
        depth_field,
        inline: false,
        closure_name: closure_name.clone(),
        trampoline,
    })
}

/// The INLINE-HashMap memo tail (rung D, `Abstractor`): key tuple
/// `(addr-of-expr cast, self.depth)` built once pre-call; `HashMap::get(&key)`
/// / hit → `cached.clone()` returned whole / miss → `stack_safe` +
/// `HashMap::insert(key, result.clone())` (evicted value dropped unread) and
/// the RESULT returned. P-ADDR / P-CLONE / P-OPT-STD positions per the module
/// doc.
#[allow(clippy::too_many_lines)]
fn match_inline_tail(
    body: &VerifiableBody,
    folder: &str,
    folder_fields: &[(String, Ty)],
    nb: &BasicBlock,
    cb: &BasicBlock,
    base_blocks: &[usize],
) -> R<WrapperFacts> {
    let ws = |d: &str| ExprFoldDecline::WrapperShape(d.to_string());
    // Key-construction block. Exactly: addr-of, opaque cast, depth copy,
    // key tuple, memo borrow, key borrow.
    let cstmts = real_stmts(cb);
    let [s_addr, s_cast, s_depth, s_key, s_memo, s_kref] = cstmts.as_slice() else {
        return Err(ws("inline memo-get block is not the pinned 6-statement key construction"));
    };
    // 1. `_a = &raw const (*_2)` — the node address (P-ADDR position).
    let Statement::Assign { place: ap, rvalue: Rvalue::AddressOf(false, asrc), .. } = s_addr else {
        return Err(ws("inline key does not start with the expr address"));
    };
    if !(ap.projections.is_empty()
        && asrc.local == 2
        && asrc.projections == vec![Projection::Deref])
    {
        return Err(ws("inline key address is not &raw const (*expr)"));
    }
    // 2. `_c = OpaqueScalar<u64>` — the authenticated restoration of the raw
    //    historical dump's erased ptr→usize cast (the P-ADDR sub-premise:
    //    this opaque scalar IS the taken address). Raw `OpaqueConst` is only
    //    an authenticated-decoder preimage and must not reach this boundary.
    let Statement::Assign {
        place: castp, rvalue: Rvalue::Use(Operand::Constant(cast_value)), ..
    } = s_cast
    else {
        return Err(ws("inline key cast is not the opaque ptr-to-usize constant"));
    };
    if !matches!(cast_value, ConstValue::OpaqueScalar { width: 64, signed: false })
        || !castp.projections.is_empty()
    {
        return Err(ws("inline key cast writes a projection"));
    }
    // 3. `_d = cp (*_1).fD` — the depth field copy (u32).
    let Statement::Assign {
        place: dp,
        rvalue: Rvalue::Use(Operand::Copy(dsrc) | Operand::Move(dsrc)),
        ..
    } = s_depth
    else {
        return Err(ws("inline key has no depth copy"));
    };
    let depth_field = match dsrc.projections.as_slice() {
        [Projection::Deref, Projection::Field(f)]
            if dsrc.local == 1 && dp.projections.is_empty() =>
        {
            *f
        }
        _ => return Err(ws("inline key depth copy is not a folder field read")),
    };
    let depth_ty_ok = folder_fields
        .get(depth_field)
        .is_some_and(|(_, fty)| matches!(fty, Ty::Int { width: 32, signed: false }));
    if !depth_ty_ok {
        return Err(ExprFoldDecline::DepthKeyUnsupported(format!(
            "inline key folder field {depth_field} is not a u32 depth field"
        )));
    }
    // 4. `_k = (mv _c, mv _d)` — the key tuple, (address, depth) in order.
    let Statement::Assign {
        place: keyp,
        rvalue: Rvalue::Aggregate(AggregateKind::Tuple, kops),
        ..
    } = s_key
    else {
        return Err(ws("inline key tuple missing"));
    };
    let key_ok = keyp.projections.is_empty()
        && matches!(kops.as_slice(), [a, b]
            if op_local(a) == Some(castp.local) && op_local(b) == Some(dp.local));
    if !key_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline key tuple is not (address-cast, depth) in order".to_string(),
        ));
    }
    let key_local = keyp.local;
    // The key local must be built exactly ONCE in the whole body (the same
    // tuple is the insert key — a rebuild between get and insert would be a
    // key-drift channel).
    let key_writes = body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.local == key_local))
        .count();
    if key_writes != 1 {
        return Err(ExprFoldDecline::KeyMismatch(format!(
            "inline memo key local written {key_writes} times (want exactly 1)"
        )));
    }
    // 5. `_m = &(*_1).fM` — the memo (HashMap) field borrow.
    let Statement::Assign {
        place: mp, rvalue: Rvalue::Ref { mutable: false, place: msrc }, ..
    } = s_memo
    else {
        return Err(ws("inline memo borrow missing"));
    };
    let memo_field = match msrc.projections.as_slice() {
        [Projection::Deref, Projection::Field(f)]
            if msrc.local == 1 && mp.projections.is_empty() =>
        {
            *f
        }
        _ => return Err(ws("inline memo borrow is not a folder field")),
    };
    let memo_ty_ok = folder_fields
        .get(memo_field)
        .is_some_and(|(_, fty)| matches!(fty, Ty::Adt { name, .. } if name == HASHMAP_TY));
    if !memo_ty_ok {
        return Err(ExprFoldDecline::ImpureState(format!(
            "inline memo folder field {memo_field} is not the pinned {HASHMAP_TY}"
        )));
    }
    if memo_field == depth_field {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline memo field collides with the depth field".to_string(),
        ));
    }
    // 6. `_kr = &_k`.
    let Statement::Assign {
        place: krp, rvalue: Rvalue::Ref { mutable: false, place: krsrc }, ..
    } = s_kref
    else {
        return Err(ws("inline key borrow missing"));
    };
    if !(krp.projections.is_empty() && is_local(krsrc, key_local)) {
        return Err(ws("inline key borrow is not of the key tuple"));
    }
    // Call `HashMap::get(mv _m, cp _kr)` (P-OPT-STD).
    let Terminator::Call { func: gcallee, args: gargs, dest: get_dest, target: Some(t2), .. } =
        &cb.terminator
    else {
        return Err(ws("no inline memo-get call"));
    };
    debug_assert_eq!(gcallee, HASHMAP_GET);
    let get_ok = matches!(gargs.as_slice(), [m, k]
        if op_local(m) == Some(mp.local) && op_local(k) == Some(krp.local))
        && get_dest.projections.is_empty();
    if !get_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline memo-get args are not (memo borrow, key borrow)".to_string(),
        ));
    }

    // hit switch (Option<&Option<Expr>> discriminant, vetted).
    let hb = block(body, *t2).ok_or_else(|| ws("missing inline hit-switch block"))?;
    let hstmts = real_stmts(hb);
    let [Statement::Assign { place: dplace, rvalue: Rvalue::Discriminant(dsrc2), .. }] =
        hstmts.as_slice()
    else {
        return Err(ws("inline hit-switch block is not exactly the discriminant read"));
    };
    if !is_local(dsrc2, get_dest.local) || !dplace.projections.is_empty() {
        return Err(ws("inline hit discriminant is not of the memo-get result"));
    }
    let Terminator::SwitchInt {
        discr: hdiscr,
        targets: htargets,
        otherwise: hother,
        exhaustive_enum_unreachable,
        ..
    } = &hb.terminator
    else {
        return Err(ws("no inline hit switch"));
    };
    if op_local(hdiscr) != Some(dplace.local) || !exhaustive_enum_unreachable {
        return Err(ws("inline hit switch is not the vetted Option discriminant switch"));
    }
    let (hit_bb, miss_bb) = match htargets.as_slice() {
        [(1, h), (0, m)] | [(0, m), (1, h)] => (*h, *m),
        _ => return Err(ws("inline hit switch targets are not the Option tags")),
    };
    let ob = block(body, *hother).ok_or_else(|| ws("missing inline hit otherwise"))?;
    if !matches!(ob.terminator, Terminator::Unreachable) {
        return Err(ws("inline hit otherwise is reachable"));
    }

    // hit arm: `_h = cp _g@V1.f0` (the `&Option<Expr>` cached ref) +
    // `Clone::clone(_h)` → _0 (the cached value cloned WHOLE — P-CLONE).
    let hitb = block(body, hit_bb).ok_or_else(|| ws("missing inline hit arm"))?;
    let hstmts2 = real_stmts(hitb);
    let [
        Statement::Assign {
            place: cp1,
            rvalue: Rvalue::Use(Operand::Move(csrc) | Operand::Copy(csrc)),
            ..
        },
    ] = hstmts2.as_slice()
    else {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline cache-hit path does not read the cached ref whole".to_string(),
        ));
    };
    let cached_ok = cp1.projections.is_empty()
        && csrc.local == get_dest.local
        && csrc.projections == vec![Projection::Downcast(1), Projection::Field(0)]
        && body.locals.get(cp1.local).is_some_and(|l| {
            matches!(&l.ty, Ty::Ref { mutable: false, inner } if is_option_of(inner, EXPR_NAME))
        });
    if !cached_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline cache-hit path does not return the cached value whole".to_string(),
        ));
    }
    let Terminator::Call { func: hc, args: hargs, dest: hdest, target: Some(hit_ret), .. } =
        &hitb.terminator
    else {
        return Err(ws("inline hit arm has no clone call"));
    };
    let hit_clone_ok = hc == CLONE_CLONE
        && matches!(hargs.as_slice(), [a] if op_local(a) == Some(cp1.local))
        && is_local(hdest, 0);
    if !hit_clone_ok {
        return Err(ExprFoldDecline::KeyMismatch("inline cache-hit clone drift".to_string()));
    }

    // miss arm: closure aggregate capturing exactly (_1, _2) + stack_safe.
    let mb = block(body, miss_bb).ok_or_else(|| ws("missing inline miss arm"))?;
    let mstmts = real_stmts(mb);
    let [
        Statement::Assign {
            place: clplace,
            rvalue: Rvalue::Aggregate(AggregateKind::Closure { name: closure_name, .. }, cl_ops),
            ..
        },
    ] = mstmts.as_slice()
    else {
        return Err(ws("inline miss arm is not exactly the closure aggregate"));
    };
    let caps_ok =
        matches!(cl_ops.as_slice(), [a, b] if op_local(a) == Some(1) && op_local(b) == Some(2));
    if !caps_ok {
        return Err(ExprFoldDecline::StackSafeDrift(
            "delegation closure does not capture exactly (folder, expr)".to_string(),
        ));
    }
    let Terminator::Call { func: sscallee, args: ssargs, dest: ss_dest, target: Some(t3), .. } =
        &mb.terminator
    else {
        return Err(ws("no inline stack_safe call"));
    };
    let ss_args_ok = matches!(ssargs.as_slice(), [a] if op_local(a) == Some(clplace.local));
    if !ss_args_ok || !ss_dest.projections.is_empty() {
        return Err(ExprFoldDecline::StackSafeDrift(
            "trampoline argument is not the delegation closure".to_string(),
        ));
    }
    let trampoline = sscallee.clone();
    let res_local = ss_dest.local;

    // insert chain: `_pm = &mut (*_1).fM; _rr = &_res;` + clone → insert →
    // drop(evicted) → `_0 = mv _res`.
    let pb = block(body, *t3).ok_or_else(|| ws("missing inline insert block"))?;
    let pstmts = real_stmts(pb);
    let [
        Statement::Assign {
            place: pmp, rvalue: Rvalue::Ref { mutable: true, place: pmsrc }, ..
        },
        Statement::Assign {
            place: rrp, rvalue: Rvalue::Ref { mutable: false, place: rrsrc }, ..
        },
    ] = pstmts.as_slice()
    else {
        return Err(ws("inline insert block statements drift"));
    };
    let pm_ok = pmp.projections.is_empty()
        && pmsrc.local == 1
        && pmsrc.projections == vec![Projection::Deref, Projection::Field(memo_field)];
    if !pm_ok {
        return Err(ExprFoldDecline::ImpureState(format!(
            "inline insert borrow is not the memo field: {pmsrc:?}"
        )));
    }
    if !(rrp.projections.is_empty() && is_local(rrsrc, res_local)) {
        return Err(ws("inline insert result borrow drift"));
    }
    let Terminator::Call { func: rc, args: rargs, dest: rcdest, target: Some(t4), .. } =
        &pb.terminator
    else {
        return Err(ws("inline insert block has no result clone"));
    };
    let rclone_ok = rc == CLONE_CLONE
        && matches!(rargs.as_slice(), [a] if op_local(a) == Some(rrp.local))
        && rcdest.projections.is_empty();
    if !rclone_ok {
        return Err(ws("inline result clone drift"));
    }
    let ib = block(body, *t4).ok_or_else(|| ws("missing inline insert call block"))?;
    if !real_stmts(ib).is_empty() {
        return Err(ws("statements before the inline insert call"));
    }
    let Terminator::Call { func: ic, args: iargs, dest: idest, target: Some(t5), .. } =
        &ib.terminator
    else {
        return Err(ws("no inline insert call"));
    };
    if ic != HASHMAP_INSERT {
        return Err(ws(&format!("inline insert callee is {ic}")));
    }
    let ins_ok = matches!(iargs.as_slice(), [m, k, v]
        if op_local(m) == Some(pmp.local)
            && op_local(k) == Some(key_local)
            && op_local(v) == Some(rcdest.local))
        && idest.projections.is_empty();
    if !ins_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline insert args are not (memo borrow, THE key tuple, result clone)".to_string(),
        ));
    }
    let evicted = idest.local;
    // The evicted Option must be dropped UNREAD: its only use anywhere is the
    // happy-path Drop.
    for b in &body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { rvalue, .. } = s {
                let mut uses_evicted = false;
                let mut chk = |op: &Operand| {
                    if op_local(op) == Some(evicted) {
                        uses_evicted = true;
                    }
                };
                match rvalue {
                    Rvalue::Use(op)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::Repeat(op, _)
                    | Rvalue::Cast(op, _) => chk(op),
                    Rvalue::BinaryOp(_, a, b2) | Rvalue::CheckedBinaryOp(_, a, b2) => {
                        chk(a);
                        chk(b2);
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().for_each(&mut chk),
                    Rvalue::Ref { place: p, .. }
                    | Rvalue::Discriminant(p)
                    | Rvalue::Len(p)
                    | Rvalue::AddressOf(_, p)
                    | Rvalue::CopyForDeref(p) => {
                        if p.local == evicted {
                            uses_evicted = true;
                        }
                    }
                    Rvalue::Unsupported { operands, .. } => operands.iter().for_each(&mut chk),
                    // `Rvalue` is non-exhaustive: an unknown kind cannot be
                    // audited for evicted-value reads — fail closed.
                    _ => {
                        return Err(ExprFoldDecline::ImpureState(
                            "unmodeled rvalue kind in the evicted-value audit".to_string(),
                        ));
                    }
                }
                if uses_evicted {
                    return Err(ExprFoldDecline::ImpureState(
                        "the inline insert's evicted value is read".to_string(),
                    ));
                }
            }
        }
        if let Terminator::Call { args, .. } = &b.terminator {
            if args.iter().any(|a| op_local(a) == Some(evicted)) {
                return Err(ExprFoldDecline::ImpureState(
                    "the inline insert's evicted value escapes into a call".to_string(),
                ));
            }
        }
    }
    // drop(evicted) → final `_0 = mv _res` → shared return.
    let db = block(body, *t5).ok_or_else(|| ws("missing inline evicted drop"))?;
    let Terminator::Drop { place: dpp, target: t6, .. } = &db.terminator else {
        return Err(ws("inline insert does not drop the evicted value"));
    };
    if !is_local(dpp, evicted) || !real_stmts(db).is_empty() {
        return Err(ws("inline evicted drop drift"));
    }
    let fb = block(body, *t6).ok_or_else(|| ws("missing inline final block"))?;
    let fin_ok = matches!(real_stmts(fb).as_slice(),
        [Statement::Assign { place, rvalue: Rvalue::Use(Operand::Move(src) | Operand::Copy(src)), .. }]
        if is_local(place, 0) && is_local(src, res_local));
    if !fin_ok {
        return Err(ExprFoldDecline::KeyMismatch(
            "inline wrapper does not return the fold result".to_string(),
        ));
    }
    let ret_bb = match &fb.terminator {
        Terminator::Return => fb.id,
        Terminator::Goto(g) => {
            let rb = block(body, *g).ok_or_else(|| ws("missing inline return block"))?;
            if !matches!(rb.terminator, Terminator::Return) || !real_stmts(rb).is_empty() {
                return Err(ws("inline final block does not flow to Return"));
            }
            *g
        }
        other => return Err(ws(&format!("inline final terminator {other:?}"))),
    };
    // The none arm and the hit arm must flow to the same shared return.
    match &nb.terminator {
        Terminator::Return => {}
        Terminator::Goto(g) if *g == ret_bb => {}
        _ => return Err(ws("none arm does not flow to Return")),
    }
    if *hit_ret != ret_bb {
        let hrb = block(body, *hit_ret).ok_or_else(|| ws("missing hit return block"))?;
        if !matches!(hrb.terminator, Terminator::Return) || !real_stmts(hrb).is_empty() {
            return Err(ws("inline hit arm does not flow to Return"));
        }
    }

    // Account for every block; the remainder must be UNWIND NOISE only
    // (empty Drop/Resume chains never assigning the return or a param).
    let mut matched: std::collections::BTreeSet<usize> = base_blocks.iter().copied().collect();
    matched.extend([
        t2.0, hother.0, hit_bb.0, hit_ret.0, miss_bb.0, t3.0, t4.0, t5.0, t6.0, fb.id.0, ret_bb.0,
    ]);
    for b in &body.blocks {
        if matched.contains(&b.id.0) {
            continue;
        }
        if !real_stmts(b).is_empty() {
            return Err(ws("inline wrapper has an unaccounted block with statements"));
        }
        match &b.terminator {
            Terminator::Resume => {}
            Terminator::Drop { place, .. } if place.local > 2 => {}
            other => {
                return Err(ws(&format!("inline wrapper unaccounted block terminator {other:?}")));
            }
        }
    }

    Ok(WrapperFacts {
        folder: folder.to_string(),
        memo_field,
        depth_field: Some(depth_field),
        inline: true,
        closure_name: closure_name.clone(),
        trampoline,
    })
}

// ===========================================================================
// Pinned co-member fingerprints: delegation closure, inner, defaults, memo
// get/put, kind/ek/from_kind, Expr::clone
// ===========================================================================

fn co_member<'a>(bodies: &'a DumpBodies, path: &str) -> R<&'a VerifiableFunction> {
    let body =
        bodies.get(path).ok_or_else(|| ExprFoldDecline::MissingCoMember(path.to_string()))?;
    if trust_vcgen::validate_function(body).is_err()
        || !crate::assignment_types::all_assignments_match(&body.body)
    {
        return Err(drift(path, "co-member fails function validation or assignment typing"));
    }
    Ok(body)
}

fn drift(member: &str, detail: impl Into<String>) -> ExprFoldDecline {
    ExprFoldDecline::CoMemberDrift { member: member.to_string(), detail: detail.into() }
}

/// The wrapper's delegation closure: `|_| fold_expr_opt_inner(cap0, cap1)`.
fn match_delegation_closure(closure: &VerifiableFunction) -> R<()> {
    let m = &closure.def_path;
    let body = &closure.body;
    if body.arg_count != 1 || body.blocks.len() != 2 {
        return Err(drift(m, "closure is not the 2-block delegation shape"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: p1,
            rvalue: Rvalue::Use(Operand::Copy(s1) | Operand::Move(s1)),
            ..
        },
        Statement::Assign {
            place: p2,
            rvalue: Rvalue::Use(Operand::Copy(s2) | Operand::Move(s2)),
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "closure statements are not the two capture reads"));
    };
    let cap_read =
        |s: &Place, f: usize| s.local == 1 && s.projections == vec![Projection::Field(f)];
    if !cap_read(s1, 0)
        || !cap_read(s2, 1)
        || !p1.projections.is_empty()
        || !p2.projections.is_empty()
    {
        return Err(drift(m, "closure does not read exactly captures .0/.1"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "closure bb0 does not end in the inner call"));
    };
    if callee != GEN_FOLD_EXPR_OPT_INNER {
        return Err(drift(m, format!("closure calls {callee}, not fold_expr_opt_inner")));
    }
    let ok = matches!(args.as_slice(), [a, b] if op_local(a) == Some(p1.local) && op_local(b) == Some(p2.local))
        && is_local(dest, 0);
    if !ok {
        return Err(drift(m, "inner call does not forward (self, expr) into _0"));
    }
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing return block"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(drift(m, "closure does not return the inner result directly"));
    }
    Ok(())
}

/// A 2-block pure delegation `f(self, x) { g(self, x) }` — used for
/// `fold_expr_opt_inner` (→ `_inner_full`) and the default
/// `fold_binder_body_opt` (→ `fold_expr_opt`).
fn match_delegation(func: &VerifiableFunction, expected_callee: &str) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 2 || body.blocks.len() != 2 {
        return Err(drift(m, "not the 2-block delegation shape"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    if !real_stmts(b0).is_empty() {
        return Err(drift(m, "unexpected statements"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "no delegation call"));
    };
    if callee != expected_callee {
        return Err(drift(m, format!("delegates to {callee}, want {expected_callee}")));
    }
    let ok = matches!(args.as_slice(), [a, b] if op_local(a) == Some(1) && op_local(b) == Some(2))
        && is_local(dest, 0);
    if !ok {
        return Err(drift(m, "delegation does not forward (self, x) into _0"));
    }
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing return block"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(drift(m, "does not return the delegate result directly"));
    }
    Ok(())
}

/// A trait-default leaf hook: single block, `_0 = Option::None; Return`.
fn match_default_none(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let ok = body.blocks.len() == 1
        && matches!(b0.terminator, Terminator::Return)
        && matches!(real_stmts(b0).as_slice(),
            [Statement::Assign { place, rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops), .. }]
            if is_local(place, 0) && name == OPTION_NAME && ops.is_empty());
    if ok { Ok(()) } else { Err(drift(m, "default is not the literal None return")) }
}

/// `Expr::kind`: `_0 = &(*_1).f0; Return`, with field 0 of `Expr` named `kind`.
fn match_expr_kind_accessor(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let ok = body.blocks.len() == 1
        && matches!(b0.terminator, Terminator::Return)
        && matches!(real_stmts(b0).as_slice(),
            [Statement::Assign { place, rvalue: Rvalue::Ref { mutable: false, place: src }, .. }]
            if is_local(place, 0)
                && src.local == 1
                && src.projections == vec![Projection::Deref, Projection::Field(0)]);
    if !ok {
        return Err(drift(m, "not the kind-field accessor shape"));
    }
    // The param's pointee field 0 must be named `kind` and be ExprKind.
    let ok_ty = matches!(body.locals.get(1).map(|l| &l.ty),
        Some(Ty::Ref { inner, .. })
        if matches!(inner.as_ref(), Ty::Adt { name, fields, .. }
            if name == EXPR_NAME
                && fields.first().is_some_and(|(fname, fty)| fname == "kind"
                    && matches!(fty, Ty::Adt { name, .. } | Ty::Datatype { name, .. } if name == EXPR_KIND_NAME))));
    if !ok_ty {
        return Err(drift(m, "kind accessor type pins failed"));
    }
    Ok(())
}

/// `ek`: pure delegation to `Expr::from_kind`.
fn match_ek(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 1 || body.blocks.len() != 2 {
        return Err(drift(m, "ek is not the 2-block delegation"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    if !real_stmts(b0).is_empty() {
        return Err(drift(m, "unexpected statements"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "no from_kind call"));
    };
    let ok = callee == EXPR_FROM_KIND
        && matches!(args.as_slice(), [a] if op_local(a) == Some(1))
        && is_local(dest, 0);
    if !ok {
        return Err(drift(m, "ek does not delegate to Expr::from_kind"));
    }
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing return"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(drift(m, "ek does not return the result directly"));
    }
    Ok(())
}

/// `Expr::from_kind`: compute_meta (META — erased by the model) + the
/// `Expr { kind: <the input, unchanged>, meta }` aggregate. The KIND-FIELD
/// PASSTHROUGH is the load-bearing check.
fn match_from_kind(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    // bb0: `_r = &_1` + call compute_meta(_r) → _meta.
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: rp, rvalue: Rvalue::Ref { mutable: false, place: rsrc }, ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "from_kind bb0 statements are not the kind borrow"));
    };
    if !is_local(rsrc, 1) {
        return Err(drift(m, "borrow is not of the kind parameter"));
    }
    let Terminator::Call { args, dest: meta_dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "no compute_meta call"));
    };
    if !matches!(args.as_slice(), [a] if op_local(a) == Some(rp.local)) {
        return Err(drift(m, "compute_meta arg is not the kind borrow"));
    }
    // next: `_k = mv _1; _0 = Expr { kind: _k, meta: _meta }; Return`.
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing aggregate block"))?;
    let s1 = real_stmts(b1);
    let [
        Statement::Assign {
            place: kp,
            rvalue: Rvalue::Use(Operand::Move(ksrc) | Operand::Copy(ksrc)),
            ..
        },
        Statement::Assign {
            place: outp,
            rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops),
            ..
        },
    ] = s1.as_slice()
    else {
        return Err(drift(m, "from_kind aggregate block shape"));
    };
    let ok = is_local(ksrc, 1)
        && kp.projections.is_empty()
        && is_local(outp, 0)
        && name == EXPR_NAME
        && matches!(ops.as_slice(), [k, mmeta]
            if op_local(k) == Some(kp.local) && op_local(mmeta) == Some(meta_dest.local));
    if !ok {
        return Err(drift(m, "from_kind does not pass the kind through unchanged"));
    }
    if !matches!(b1.terminator, Terminator::Return) {
        return Err(drift(m, "from_kind aggregate block does not return"));
    }
    Ok(())
}

/// `FoldMemo::get`: address-key lookup + `Option::<&T>::cloned` (P-ADDR /
/// P-CLONE positions; see the module doc).
fn match_memo_get(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 3 {
        return Err(drift(m, "get arity"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    // `_map = &(*_1).f0; _addr = &raw const (*_2);`
    // `_k0 = OpaqueScalar<u64>` (authenticated canonical form);
    //  _key = (mv _k0, cp _3); _kr = &_key;` + HashMap::get(_map, _kr).
    let [
        Statement::Assign {
            place: mapp,
            rvalue: Rvalue::Ref { mutable: false, place: mapsrc },
            ..
        },
        Statement::Assign { place: _addrp, rvalue: Rvalue::AddressOf(false, addrsrc), .. },
        Statement::Assign { place: k0p, rvalue: Rvalue::Use(Operand::Constant(k0_value)), .. },
        Statement::Assign {
            place: keyp,
            rvalue: Rvalue::Aggregate(AggregateKind::Tuple, keyops),
            ..
        },
        Statement::Assign {
            place: krp, rvalue: Rvalue::Ref { mutable: false, place: krsrc }, ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "get bb0 is not the pinned key construction"));
    };
    let ok = mapsrc.local == 1
        && matches!(k0_value, ConstValue::OpaqueScalar { width: 64, signed: false })
        && mapsrc.projections == vec![Projection::Deref, Projection::Field(0)]
        && addrsrc.local == 2
        && addrsrc.projections == vec![Projection::Deref]
        && matches!(keyops.as_slice(), [a, b]
            if op_local(a) == Some(k0p.local) && op_local(b) == Some(3))
        && is_local(krsrc, keyp.local);
    if !ok {
        return Err(drift(m, "get key construction drift"));
    }
    let Terminator::Call { func: c1, args: a1, dest: d1, target: Some(t1), .. } = &b0.terminator
    else {
        return Err(drift(m, "no HashMap::get call"));
    };
    if c1 != HASHMAP_GET
        || !matches!(a1.as_slice(), [x, y] if op_local(x) == Some(mapp.local) && op_local(y) == Some(krp.local))
    {
        return Err(drift(m, "HashMap::get call drift"));
    }
    let b1 = block(body, *t1).ok_or_else(|| drift(m, "missing cloned block"))?;
    let Terminator::Call { func: c2, args: a2, dest: d2, target: Some(t2), .. } = &b1.terminator
    else {
        return Err(drift(m, "no Option::cloned call"));
    };
    let ok2 = real_stmts(b1).is_empty()
        && c2 == OPTION_CLONED
        && matches!(a2.as_slice(), [x] if op_local(x) == Some(d1.local))
        && is_local(d2, 0);
    if !ok2 {
        return Err(drift(m, "Option::cloned drift"));
    }
    let b2 = block(body, *t2).ok_or_else(|| drift(m, "missing return"))?;
    if !matches!(b2.terminator, Terminator::Return) || !real_stmts(b2).is_empty() {
        return Err(drift(m, "get does not return the cloned hit directly"));
    }
    Ok(())
}

/// `FoldMemo::put`: same key construction + `result.clone()` insert + the
/// RESULT (not the clone) returned; the insert's evicted-value Option is
/// dropped unread.
fn match_memo_put(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 4 {
        return Err(drift(m, "put arity"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: mapp, rvalue: Rvalue::Ref { mutable: true, place: mapsrc }, ..
        },
        Statement::Assign { place: _addrp, rvalue: Rvalue::AddressOf(false, addrsrc), .. },
        Statement::Assign { place: k0p, rvalue: Rvalue::Use(Operand::Constant(k0_value)), .. },
        Statement::Assign {
            place: keyp,
            rvalue: Rvalue::Aggregate(AggregateKind::Tuple, keyops),
            ..
        },
        Statement::Assign {
            place: vrp, rvalue: Rvalue::Ref { mutable: false, place: vrsrc }, ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "put bb0 is not the pinned key+clone construction"));
    };
    let ok = mapsrc.local == 1
        && matches!(k0_value, ConstValue::OpaqueScalar { width: 64, signed: false })
        && mapsrc.projections == vec![Projection::Deref, Projection::Field(0)]
        && addrsrc.local == 2
        && addrsrc.projections == vec![Projection::Deref]
        && matches!(keyops.as_slice(), [a, b]
            if op_local(a) == Some(k0p.local) && op_local(b) == Some(3))
        && is_local(vrsrc, 4);
    if !ok {
        return Err(drift(m, "put key/value construction drift"));
    }
    let Terminator::Call { func: c1, args: a1, dest: clone_dest, target: Some(t1), .. } =
        &b0.terminator
    else {
        return Err(drift(m, "no result clone call"));
    };
    if c1 != CLONE_CLONE || !matches!(a1.as_slice(), [x] if op_local(x) == Some(vrp.local)) {
        return Err(drift(m, "result clone drift (P-CLONE position)"));
    }
    let b1 = block(body, *t1).ok_or_else(|| drift(m, "missing insert block"))?;
    let Terminator::Call { func: c2, args: a2, dest: ins_dest, target: Some(t2), .. } =
        &b1.terminator
    else {
        return Err(drift(m, "no HashMap::insert call"));
    };
    let ok2 = real_stmts(b1).is_empty()
        && c2 == HASHMAP_INSERT
        && matches!(a2.as_slice(), [x, y, z]
            if op_local(x) == Some(mapp.local)
                && op_local(y) == Some(keyp.local)
                && op_local(z) == Some(clone_dest.local));
    if !ok2 {
        return Err(drift(m, "HashMap::insert drift"));
    }
    // Drop of the evicted Option (unread), then `_0 = mv _4; Return`.
    let b2 = block(body, *t2).ok_or_else(|| drift(m, "missing drop block"))?;
    let Terminator::Drop { place: dropped, target: t3, .. } = &b2.terminator else {
        return Err(drift(m, "insert result is not dropped unread"));
    };
    if !is_local(dropped, ins_dest.local) || !real_stmts(b2).is_empty() {
        return Err(drift(m, "insert-result drop drift"));
    }
    let b3 = block(body, *t3).ok_or_else(|| drift(m, "missing return block"))?;
    let ret_ok = matches!(b3.terminator, Terminator::Return)
        && matches!(real_stmts(b3).as_slice(),
            [Statement::Assign { place, rvalue: Rvalue::Use(Operand::Move(src) | Operand::Copy(src)), .. }]
            if is_local(place, 0) && is_local(src, 4));
    if !ret_ok {
        return Err(drift(m, "put does not return the RESULT argument"));
    }
    Ok(())
}

/// Rung D: `expr::checked_add_u32` (P-SAT-ADD fingerprint) — the exact
/// two-block forwarding to `core::num::<impl u32>::saturating_add(a, b)`
/// (the `_context` string is dead). The real depth successor is therefore
/// the u32-SATURATING successor (std semantics premise).
fn match_checked_add_u32(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 3 || body.blocks.len() != 2 {
        return Err(drift(m, "checked_add_u32 shape"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    if !real_stmts(b0).is_empty() {
        return Err(drift(m, "checked_add_u32 has statements"));
    }
    let Terminator::Call { func: c, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "checked_add_u32 does not forward"));
    };
    let ok = c == SATURATING_ADD_U32
        && matches!(args.as_slice(), [a, b] if op_local(a) == Some(1) && op_local(b) == Some(2))
        && is_local(dest, 0);
    if !ok {
        return Err(drift(m, "checked_add_u32 forwarding drift (P-SAT-ADD)"));
    }
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing return"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(drift(m, "checked_add_u32 does not return the sum"));
    }
    Ok(())
}

/// Rung D: the folder's `fold_binder_body_opt` override — the EXACT
/// save/`checked_add_u32(+1)`/call/restore pattern (design §2 discipline
/// (ii): the depth field's ONLY writes anywhere in the SCC):
///
/// ```text
/// bb0: _s = cp (*_1).fD ; _a = cp (*_1).fD
///      Call _i = expr::checked_add_u32(mv _a, const 1u32, const <str>) → bb1
/// bb1: (*_1).fD = mv _i
///      Call _0 = ExprFolderOpt::fold_expr_opt(cp _1, cp _2) → bb2
/// bb2: (*_1).fD = cp _s ; Return
/// ```
///
/// Named declines: a missing/wrong restore → `fold_memo::missing_restore`;
/// a write outside the pattern → `fold_memo::impure_state`; a field other
/// than the memo-key depth field → `fold_memo::key_mismatch`; anything else
/// → `binder_body_shape`.
fn match_binder_body_override(func: &VerifiableFunction, depth_field: usize) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    let bs = |d: &str| ExprFoldDecline::BinderBodyShape(format!("{m}: {d}"));
    if body.arg_count != 2 {
        return Err(bs("arity"));
    }
    if !is_option_of(&body.return_ty, EXPR_NAME) {
        return Err(bs("return type is not Option<Expr>"));
    }
    if body.blocks.len() != 3 {
        return Err(bs("not the pinned 3-block save/inc/call/restore shape"));
    }
    let dproj = vec![Projection::Deref, Projection::Field(depth_field)];

    // bb0: the two entry-depth copies + the saturating increment call.
    let b0 = block(body, BlockId(0)).ok_or_else(|| bs("no bb0"))?;
    let s0 = real_stmts(b0);
    let [
        Statement::Assign {
            place: savep,
            rvalue: Rvalue::Use(Operand::Copy(savesrc) | Operand::Move(savesrc)),
            ..
        },
        Statement::Assign {
            place: argp,
            rvalue: Rvalue::Use(Operand::Copy(argsrc) | Operand::Move(argsrc)),
            ..
        },
    ] = s0.as_slice()
    else {
        return Err(bs("bb0 is not exactly the save + increment-arg depth copies"));
    };
    for (p, src) in [(savep, savesrc), (argp, argsrc)] {
        if !p.projections.is_empty() || src.local != 1 {
            return Err(bs("depth copy shape drift"));
        }
        if src.projections != dproj {
            return Err(ExprFoldDecline::KeyMismatch(format!(
                "{m}: binder body threads {src:?}, not the memo-key depth field {depth_field}"
            )));
        }
    }
    let save_local = savep.local;
    let Terminator::Call { func: c0, args: a0, dest: inc_dest, target: Some(t1), .. } =
        &b0.terminator
    else {
        return Err(bs("bb0 does not end in the increment call"));
    };
    if c0 != CHECKED_ADD_U32 {
        return Err(bs(&format!("increment callee is {c0}, not {CHECKED_ADD_U32}")));
    }
    let inc_ok = matches!(a0.as_slice(), [d, one, _msg]
        if op_local(d) == Some(argp.local)
            && matches!(one, Operand::Constant(ConstValue::Uint(1, 32))))
        && inc_dest.projections.is_empty();
    if !inc_ok {
        return Err(bs("increment args are not (entry depth, const 1u32, <msg>)"));
    }

    // bb1: the increment write + the SCC recursion into fold_expr_opt.
    let b1 = block(body, *t1).ok_or_else(|| bs("missing bb1"))?;
    let s1 = real_stmts(b1);
    let [
        Statement::Assign {
            place: wp,
            rvalue: Rvalue::Use(Operand::Move(wsrc) | Operand::Copy(wsrc)),
            ..
        },
    ] = s1.as_slice()
    else {
        return Err(ExprFoldDecline::ImpureState(format!(
            "{m}: bb1 is not exactly the depth increment write"
        )));
    };
    if !(wp.local == 1 && wp.projections == dproj) {
        return Err(ExprFoldDecline::ImpureState(format!(
            "{m}: bb1 writes {wp:?}, not the depth field"
        )));
    }
    if !is_local(wsrc, inc_dest.local) {
        return Err(bs("the depth write is not the increment result"));
    }
    let Terminator::Call { func: c1, args: a1, dest: call_dest, target: Some(t2), .. } =
        &b1.terminator
    else {
        return Err(bs("bb1 does not end in the fold_expr_opt call"));
    };
    if c1 != GEN_FOLD_EXPR_OPT {
        return Err(bs(&format!("recursion callee is {c1}, not fold_expr_opt")));
    }
    let call_ok = matches!(a1.as_slice(), [s, e]
        if op_local(s) == Some(1) && op_local(e) == Some(2))
        && is_local(call_dest, 0);
    if !call_ok {
        return Err(bs("fold_expr_opt call args/dest drift"));
    }

    // bb2: the restore + Return.
    let b2 = block(body, *t2).ok_or_else(|| bs("missing bb2"))?;
    let s2 = real_stmts(b2);
    match s2.as_slice() {
        [
            Statement::Assign {
                place: rp,
                rvalue: Rvalue::Use(Operand::Copy(rsrc) | Operand::Move(rsrc)),
                ..
            },
        ] => {
            if !(rp.local == 1 && rp.projections == dproj) {
                return Err(ExprFoldDecline::ImpureState(format!(
                    "{m}: the post-call write is not the depth restore: {rp:?}"
                )));
            }
            if !is_local(rsrc, save_local) {
                return Err(ExprFoldDecline::MissingRestore(format!(
                    "{m}: the restore does not write back the saved entry depth"
                )));
            }
        }
        [] => {
            return Err(ExprFoldDecline::MissingRestore(format!(
                "{m}: no depth restore after the recursive call"
            )));
        }
        _ => {
            return Err(ExprFoldDecline::ImpureState(format!(
                "{m}: extra statements around the depth restore"
            )));
        }
    }
    if !matches!(b2.terminator, Terminator::Return) {
        return Err(bs("restore block does not Return"));
    }
    Ok(())
}

/// Rung D, the C-family ROW entry: recognize a standalone
/// `fold_binder_body_opt` override row and return `(folder, depth_field)`.
/// The row's certificate is the SCC's (the gate arm re-runs the full SCC
/// recognition from the folder's `fold_expr_opt` wrapper co-member).
pub fn sem_binder_body_row_of(
    func: &VerifiableFunction,
) -> Result<(String, usize), ExprFoldDecline> {
    if !func.def_path.ends_with(">::fold_binder_body_opt") {
        return Err(ExprFoldDecline::SignatureUnsupported(
            "not a fold_binder_body_opt row".to_string(),
        ));
    }
    let Some(Ty::Ref { mutable: true, inner }) = func.body.locals.get(1).map(|l| &l.ty) else {
        return Err(ExprFoldDecline::SignatureUnsupported(
            "param 1 is not &mut Folder".to_string(),
        ));
    };
    let Ty::Adt { name: folder, fields, .. } = inner.as_ref() else {
        return Err(ExprFoldDecline::SignatureUnsupported("folder is not a struct".to_string()));
    };
    // Discover the depth field from the save copy, then pin the full shape.
    let b0 = block(&func.body, BlockId(0))
        .ok_or_else(|| ExprFoldDecline::BinderBodyShape("no entry block".to_string()))?;
    let depth_field = real_stmts(b0)
        .first()
        .and_then(|s| match s {
            Statement::Assign {
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } if src.local == 1 => match src.projections.as_slice() {
                [Projection::Deref, Projection::Field(f)] => Some(*f),
                _ => None,
            },
            _ => None,
        })
        .ok_or_else(|| {
            ExprFoldDecline::BinderBodyShape(
                "entry does not start with the depth save copy".to_string(),
            )
        })?;
    let depth_ty_ok = fields
        .get(depth_field)
        .is_some_and(|(_, fty)| matches!(fty, Ty::Int { width: 32, signed: false }));
    if !depth_ty_ok {
        return Err(ExprFoldDecline::BinderBodyShape(format!(
            "saved folder field {depth_field} is not a u32 depth field"
        )));
    }
    match_binder_body_override(func, depth_field)?;
    Ok((folder.clone(), depth_field))
}

/// `Expr::clone` (P-CLONE fingerprint): `ExprKind::clone(kind-ref)` + the
/// `Expr { kind: cloned, meta: copied }` aggregate — kind passthrough via the
/// kind clone, meta a Copy.
pub(crate) fn match_expr_clone(func: &VerifiableFunction) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: krp, rvalue: Rvalue::Ref { mutable: false, place: krsrc }, ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "Expr::clone bb0 statements"));
    };
    if !(krsrc.local == 1 && krsrc.projections == vec![Projection::Deref, Projection::Field(0)]) {
        return Err(drift(m, "Expr::clone does not borrow the kind field"));
    }
    let Terminator::Call { func: c1, args: a1, dest: kd, target: Some(t1), .. } = &b0.terminator
    else {
        return Err(drift(m, "no kind clone call"));
    };
    // The callee renders as the GENERIC `Clone::clone`; the resolution pin is
    // the argument's declared type `&ExprKind` (P-CLONE).
    if c1 != CLONE_CLONE {
        return Err(drift(m, format!("kind clone callee is {c1}")));
    }
    if !matches!(a1.as_slice(), [x] if op_local(x) == Some(krp.local)) {
        return Err(drift(m, "kind clone arg drift"));
    }
    let arg_ty_ok = body.locals.get(krp.local).is_some_and(|l| {
        matches!(&l.ty, Ty::Ref { mutable: false, inner }
            if crate::trustir_fold::ty_names_enum(inner, EXPR_KIND_NAME))
    });
    if !arg_ty_ok {
        return Err(drift(m, "kind clone arg is not &ExprKind"));
    }
    let b1 = block(body, *t1).ok_or_else(|| drift(m, "missing aggregate block"))?;
    let s1 = real_stmts(b1);
    let [
        Statement::Assign {
            place: mp,
            rvalue: Rvalue::Use(Operand::Copy(msrc) | Operand::Move(msrc)),
            ..
        },
        Statement::Assign {
            place: outp,
            rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops),
            ..
        },
    ] = s1.as_slice()
    else {
        return Err(drift(m, "Expr::clone aggregate block shape"));
    };
    let ok = msrc.local == 1
        && msrc.projections == vec![Projection::Deref, Projection::Field(1)]
        && is_local(outp, 0)
        && name == EXPR_NAME
        && matches!(ops.as_slice(), [k, mm]
            if op_local(k) == Some(kd.local) && op_local(mm) == Some(mp.local));
    if !ok || !matches!(b1.terminator, Terminator::Return) {
        return Err(drift(m, "Expr::clone does not rebuild {kind: clone, meta: copy}"));
    }
    Ok(())
}

// ===========================================================================
// The generic dispatch walk — inner_full / extensions / zfc / fold_zfc
// ===========================================================================

/// Abstract value a walked local holds during one arm walk.
#[derive(Debug, Clone, PartialEq, Eq)]
enum V {
    /// The `self` (folder) parameter.
    SelfRef,
    /// The `&Expr` parameter of the enclosing generic body.
    ExprParam,
    /// `&scrut@V{v}.f{i}` — the matched variant's field ref.
    FieldRef(usize),
    /// Payload copied out by value (`cp (*FieldRef)`).
    PayloadVal(usize),
    /// `&Expr` strict-subterm handle (Arc-deref of a rec field).
    SubtermRef(usize),
    /// `Option<Expr>` result of the SCC fold of child `f`.
    Folded(usize),
    /// A shared reference to another tracked value.
    RefOf(Box<V>),
    /// A tuple of tracked values.
    Tuple(Vec<V>),
    /// The discriminant of `Folded(f)` (zfc inline merge).
    DiscrOf(usize),
    /// A closure aggregate.
    Closure { name: String, caps: Vec<V> },
    /// `Option<ZFCSetExpr>` result of `fold_zfc_set_expr_opt`.
    ZfcFolded,
    /// Picked `Arc<Expr>` (map_or_else of `Folded(f)` in the zfc inline merge).
    Picked(usize),
}

/// How field refs project off the scrutinee in one dispatch body.
#[derive(Clone, Copy)]
enum ScrutBase {
    /// `&(*kind_local)@V{v}.f{i}` — inner_full/extensions/zfc (kind accessor
    /// result).
    KindRef(usize),
    /// `&(*param2)@V{v}.f{i}` — fold_zfc_set_expr_opt's own `&ZFCSetExpr`
    /// param.
    Param2,
}

/// What one arm walk concluded.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ArmOutcome {
    Arm(TArm),
    /// `fold_expr_opt_extensions(self, expr)` → `_0` (inner_full only).
    HopExtensions,
    /// `fold_expr_opt_zfc(self, expr)` → `_0` (extensions only).
    HopZfc,
    /// The ZFCSet arm: `fold_zfc_set_expr_opt(self, &field0)` +
    /// `Option::map(·, <ZST ZFCSet∘ek wrap>)` → `_0` (zfc only).
    ZfcSetDispatch,
}

struct WalkCtx<'a> {
    member: &'a str,
    body: &'a VerifiableBody,
    dropflags: &'a std::collections::BTreeSet<usize>,
    scrut: ScrutBase,
    variant: &'a DumpVariant,
    v_idx: usize,
}

fn arm_err(ctx: &WalkCtx<'_>, detail: impl Into<String>) -> ExprFoldDecline {
    ExprFoldDecline::ArmShape {
        variant: format!("{}::{}", ctx.member, ctx.variant.name),
        detail: detail.into(),
    }
}

/// Whether `place` is the matched variant's field projection under the walk's
/// scrutinee base; returns the field index.
fn scrut_field(ctx: &WalkCtx<'_>, place: &Place) -> Option<usize> {
    let (base, v, f) = match (ctx.scrut, place.projections.as_slice()) {
        (
            ScrutBase::KindRef(k),
            [Projection::Deref, Projection::Downcast(v), Projection::Field(f)],
        ) if place.local == k => (true, *v, *f),
        (ScrutBase::Param2, [Projection::Deref, Projection::Downcast(v), Projection::Field(f)])
            if place.local == 2 =>
        {
            (true, *v, *f)
        }
        _ => (false, 0, 0),
    };
    if base && v == ctx.v_idx { Some(f) } else { None }
}

/// Resolve an operand against the walk bindings.
fn resolve(ctx: &WalkCtx<'_>, map: &BTreeMap<usize, V>, op: &Operand) -> R<V> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => {
            if let Some(f) = scrut_field(ctx, p) {
                // A by-ref projection appears only under Rvalue::Ref; a
                // by-VALUE copy of a variant field is a payload move the
                // vocabulary does not include.
                return Err(arm_err(ctx, format!("by-value variant field use .f{f}")));
            }
            match p.projections.as_slice() {
                [] => {
                    if p.local == 1 {
                        return Ok(V::SelfRef);
                    }
                    if p.local == 2 && matches!(ctx.scrut, ScrutBase::KindRef(_)) {
                        return Ok(V::ExprParam);
                    }
                    map.get(&p.local)
                        .cloned()
                        .ok_or_else(|| arm_err(ctx, format!("use of untracked local _{}", p.local)))
                }
                [Projection::Deref] => match map.get(&p.local) {
                    Some(V::FieldRef(f))
                        if ctx.variant.fields.get(*f) == Some(&TField::Payload) =>
                    {
                        Ok(V::PayloadVal(*f))
                    }
                    other => Err(arm_err(ctx, format!("deref of {other:?}"))),
                },
                [Projection::Field(i)] => match map.get(&p.local) {
                    Some(V::Tuple(elems)) => elems
                        .get(*i)
                        .cloned()
                        .ok_or_else(|| arm_err(ctx, "tuple projection out of range")),
                    other => Err(arm_err(ctx, format!("field projection of {other:?}"))),
                },
                _ => Err(arm_err(ctx, format!("unmodeled operand place {p:?}"))),
            }
        }
        Operand::Constant(c) => Err(arm_err(ctx, format!("unmodeled constant operand {c:?}"))),
        other => Err(arm_err(ctx, format!("unmodeled operand {other:?}"))),
    }
}

/// The variant's recursive / payload field index lists, in declaration order.
fn rec_fields(v: &DumpVariant) -> Vec<usize> {
    v.fields.iter().enumerate().filter(|(_, k)| **k == TField::Rec).map(|(i, _)| i).collect()
}
fn payload_fields(v: &DumpVariant) -> Vec<usize> {
    v.fields.iter().enumerate().filter(|(_, k)| **k == TField::Payload).map(|(i, _)| i).collect()
}

/// Verify the arm epilogue from `bb`: after `_0` is assigned, only drop-flag
/// writes, drop-flag switches, drops of temporaries, and gotos may occur
/// before `Return`. Fail-closed on anything else.
fn check_epilogue(
    ctx: &WalkCtx<'_>,
    bb: BlockId,
    visited: &mut std::collections::BTreeSet<usize>,
) -> R<()> {
    if !visited.insert(bb.0) {
        return Ok(());
    }
    let b = block(ctx.body, bb).ok_or_else(|| arm_err(ctx, "missing epilogue block"))?;
    for s in real_stmts(&b) {
        match s {
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                ..
            } if place.projections.is_empty() && ctx.dropflags.contains(&place.local) => {}
            other => {
                return Err(arm_err(ctx, format!("non-noise epilogue statement {other:?}")));
            }
        }
    }
    match &b.terminator {
        Terminator::Return => Ok(()),
        Terminator::Goto(next) => check_epilogue(ctx, *next, visited),
        Terminator::Drop { place, target, .. } => {
            if place.local <= 2 {
                return Err(arm_err(ctx, "epilogue drops a parameter/return local"));
            }
            check_epilogue(ctx, *target, visited)
        }
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let Some(l) = op_local(discr) else {
                return Err(arm_err(ctx, "epilogue switch on a projected selector"));
            };
            if !ctx.dropflags.contains(&l) {
                return Err(arm_err(ctx, "epilogue switch on a non-drop-flag local"));
            }
            for (_, t) in targets {
                check_epilogue(ctx, *t, visited)?;
            }
            check_epilogue(ctx, *otherwise, visited)
        }
        other => Err(arm_err(ctx, format!("unmodeled epilogue terminator {other:?}"))),
    }
}

/// The result of matching one `merge*`/`Option::map` make operand.
enum MakeKind {
    /// Named capturing closure — body walked, fully observable.
    NamedClosure(String, Vec<V>),
    /// Extractor-authenticated non-capturing closure or function item.
    Callable(String, CallableKind, CallableDefPathHash),
}

/// Walk ONE dispatch arm. `expect_hops` gates which hop outcomes are legal in
/// this body.
#[allow(clippy::too_many_lines)]
fn walk_arm(
    ctx: &WalkCtx<'_>,
    bodies: &DumpBodies,
    start: BlockId,
    allow_hop_extensions: bool,
    allow_hop_zfc: bool,
    allow_zfc_set: bool,
) -> R<ArmOutcome> {
    let mut map: BTreeMap<usize, V> = BTreeMap::new();
    let mut folded: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    // Rung D: which folded children went through `fold_binder_body_opt`
    // (the (d+1) IH slot). A dispatch fact read off the real MIR.
    let mut folded_binder: BTreeMap<usize, bool> = BTreeMap::new();
    let mut cur = start;
    let mut guard = 0usize;

    loop {
        guard += 1;
        if guard > 64 {
            return Err(arm_err(ctx, "arm walk exceeded the block budget"));
        }
        let b = block(ctx.body, cur).ok_or_else(|| arm_err(ctx, "missing arm block"))?;

        for s in real_stmts(&b) {
            match s {
                Statement::Assign { place, rvalue, .. } => {
                    if !place.projections.is_empty() {
                        return Err(arm_err(ctx, "projected place write in an arm"));
                    }
                    // Drop-flag noise.
                    if matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Bool(_))))
                        && ctx.dropflags.contains(&place.local)
                    {
                        continue;
                    }
                    let val: V = match rvalue {
                        Rvalue::Ref { mutable: false, place: p } => {
                            if let Some(f) = scrut_field(ctx, p) {
                                V::FieldRef(f)
                            } else if p.projections.is_empty() {
                                let inner = map.get(&p.local).cloned().ok_or_else(|| {
                                    arm_err(ctx, format!("borrow of untracked local _{}", p.local))
                                })?;
                                V::RefOf(Box::new(inner))
                            } else {
                                return Err(arm_err(
                                    ctx,
                                    format!("borrow of unmodeled place {p:?}"),
                                ));
                            }
                        }
                        Rvalue::Ref { mutable: true, .. } => {
                            return Err(ExprFoldDecline::ImpureState(format!(
                                "mutable borrow inside {}::{} arm",
                                ctx.member, ctx.variant.name
                            )));
                        }
                        Rvalue::Use(op) => resolve(ctx, &map, op)?,
                        Rvalue::Aggregate(AggregateKind::Closure { name, .. }, ops) => {
                            let mut caps = Vec::with_capacity(ops.len());
                            for op in ops {
                                caps.push(resolve(ctx, &map, op)?);
                            }
                            V::Closure { name: name.clone(), caps }
                        }
                        Rvalue::Aggregate(AggregateKind::Tuple, ops) => {
                            let mut elems = Vec::with_capacity(ops.len());
                            for op in ops {
                                elems.push(resolve(ctx, &map, op)?);
                            }
                            V::Tuple(elems)
                        }
                        Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, ops) => {
                            if name == OPTION_NAME && *variant == 0 && ops.is_empty() {
                                // `_0 = None` — only legal as THE return write
                                // of a none-arm; recorded via place check below.
                                if place.local != 0 {
                                    return Err(arm_err(ctx, "None built into a temp"));
                                }
                                // Must be the FINAL real statement (no
                                // post-write smuggling in the same block).
                                let stmts = real_stmts(b);
                                if !std::ptr::eq(*stmts.last().expect("nonempty"), s) {
                                    return Err(arm_err(
                                        ctx,
                                        "statements after the None return write",
                                    ));
                                }
                                // The arm is a NoneArm; verify epilogue.
                                let epi = match &b.terminator {
                                    Terminator::Goto(next) => *next,
                                    Terminator::Return => {
                                        return Ok(ArmOutcome::Arm(TArm::NoneArm));
                                    }
                                    other => {
                                        return Err(arm_err(
                                            ctx,
                                            format!("none-arm terminator {other:?}"),
                                        ));
                                    }
                                };
                                let mut seen = std::collections::BTreeSet::new();
                                check_epilogue(ctx, epi, &mut seen)?;
                                // Only the None write may precede.
                                return Ok(ArmOutcome::Arm(TArm::NoneArm));
                            }
                            return Err(arm_err(
                                ctx,
                                format!("unmodeled aggregate {name} variant {variant}"),
                            ));
                        }
                        Rvalue::Discriminant(p) => {
                            let ok = p.projections == vec![Projection::Deref];
                            let inner = ok.then(|| map.get(&p.local)).flatten();
                            match inner {
                                Some(V::RefOf(v)) => match v.as_ref() {
                                    V::Folded(f) => V::DiscrOf(*f),
                                    other => {
                                        return Err(arm_err(
                                            ctx,
                                            format!("discriminant of {other:?}"),
                                        ));
                                    }
                                },
                                other => {
                                    return Err(arm_err(ctx, format!("discriminant of {other:?}")));
                                }
                            }
                        }
                        other => {
                            return Err(arm_err(ctx, format!("unmodeled rvalue {other:?}")));
                        }
                    };
                    map.insert(place.local, val);
                }
                other => return Err(arm_err(ctx, format!("unmodeled statement {other:?}"))),
            }
        }

        match &b.terminator {
            Terminator::Goto(next) => {
                cur = *next;
            }
            Terminator::Return => {
                return Err(arm_err(ctx, "arm returned without producing a result"));
            }
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
                exhaustive_enum_unreachable,
                ..
            } => {
                // The zfc inline any-some merge (Pair/Separation/Replacement).
                let Some(dl) = op_local(discr) else {
                    return Err(arm_err(ctx, "switch on a projected selector"));
                };
                let Some(V::DiscrOf(first)) = map.get(&dl).cloned() else {
                    return Err(arm_err(ctx, "switch on a non-fold-discriminant selector"));
                };
                if !allow_zfc_set {
                    return Err(arm_err(ctx, "inline merge outside the zfc dispatch"));
                }
                return walk_zfc_inline_merge(
                    ctx,
                    bodies,
                    &map,
                    &folded,
                    &folded_binder,
                    first,
                    targets,
                    *otherwise,
                    *exhaustive_enum_unreachable,
                );
            }
            Terminator::Call { func: callee, args, dest, target, .. } => {
                let Some(target) = target else {
                    return Err(arm_err(ctx, "diverging call"));
                };
                if !dest.projections.is_empty() {
                    return Err(arm_err(ctx, "projected call destination"));
                }
                // Resolve args lazily per callee class below.
                let is_self = |op: &Operand| matches!(resolve(ctx, &map, op), Ok(V::SelfRef));

                if callee == ARC_DEREF {
                    let [a] = args.as_slice() else {
                        return Err(arm_err(ctx, "deref arity"));
                    };
                    let Ok(V::FieldRef(f)) = resolve(ctx, &map, a) else {
                        return Err(arm_err(ctx, "deref of a non-field ref"));
                    };
                    if ctx.variant.fields.get(f) != Some(&TField::Rec) {
                        return Err(arm_err(ctx, format!("deref of non-recursive field {f}")));
                    }
                    // P-ARC-DEREF type pins on this body's own locals.
                    let arg_ok =
                        op_local(a).and_then(|l| ctx.body.locals.get(l)).is_some_and(|l| {
                            matches!(&l.ty, Ty::Ref { mutable: false, inner }
                            if crate::trustir_fold::arc_pointee_ty(inner)
                                .is_some_and(|p| crate::trustir_fold::ty_names_enum(p, EXPR_NAME)))
                        });
                    let dest_ok = ctx.body.locals.get(dest.local).is_some_and(|l| {
                        matches!(&l.ty, Ty::Ref { mutable: false, inner }
                            if crate::trustir_fold::ty_names_enum(inner, EXPR_NAME))
                    });
                    if !arg_ok || !dest_ok {
                        return Err(arm_err(ctx, "Deref::deref type pins failed (P-ARC-DEREF)"));
                    }
                    map.insert(dest.local, V::SubtermRef(f));
                    cur = *target;
                    continue;
                }

                if callee == GEN_FOLD_EXPR_OPT || callee == GEN_FOLD_BINDER_BODY_OPT {
                    let [s, n] = args.as_slice() else {
                        return Err(arm_err(ctx, "fold call arity"));
                    };
                    if !is_self(s) {
                        return Err(arm_err(ctx, "fold call receiver is not self"));
                    }
                    let f = match resolve(ctx, &map, n)? {
                        V::SubtermRef(f) => f,
                        V::ExprParam => {
                            return Err(ExprFoldDecline::NonSubtermRecursiveArg(format!(
                                "{}::{}: recursion on the scrutinee itself",
                                ctx.member, ctx.variant.name
                            )));
                        }
                        other => {
                            return Err(ExprFoldDecline::NonSubtermRecursiveArg(format!(
                                "{}::{}: recursion on {other:?}",
                                ctx.member, ctx.variant.name
                            )));
                        }
                    };
                    if !folded.insert(f) {
                        return Err(ExprFoldDecline::DuplicateRecursiveCall(format!(
                            "{}::{} folds field {f} twice",
                            ctx.member, ctx.variant.name
                        )));
                    }
                    folded_binder.insert(f, callee == GEN_FOLD_BINDER_BODY_OPT);
                    map.insert(dest.local, V::Folded(f));
                    cur = *target;
                    continue;
                }

                if callee == GEN_FOLD_EXPR_OPT_EXTENSIONS && allow_hop_extensions {
                    let ok = matches!(args.as_slice(), [s, e]
                        if is_self(s) && matches!(resolve(ctx, &map, e), Ok(V::ExprParam)))
                        && is_local(dest, 0);
                    if !ok {
                        return Err(arm_err(ctx, "extensions hop args drift"));
                    }
                    let mut seen = std::collections::BTreeSet::new();
                    check_epilogue(ctx, *target, &mut seen)?;
                    return Ok(ArmOutcome::HopExtensions);
                }
                if callee == GEN_FOLD_EXPR_OPT_ZFC && allow_hop_zfc {
                    let ok = matches!(args.as_slice(), [s, e]
                        if is_self(s) && matches!(resolve(ctx, &map, e), Ok(V::ExprParam)))
                        && is_local(dest, 0);
                    if !ok {
                        return Err(arm_err(ctx, "zfc hop args drift"));
                    }
                    let mut seen = std::collections::BTreeSet::new();
                    check_epilogue(ctx, *target, &mut seen)?;
                    return Ok(ArmOutcome::HopZfc);
                }

                if callee == GEN_FOLD_ZFC_SET_EXPR_OPT && allow_zfc_set {
                    // ZFCSet arm: fold the DIRECT ZFCSetExpr payload field.
                    let [s, n] = args.as_slice() else {
                        return Err(arm_err(ctx, "zfc-set fold arity"));
                    };
                    let ok = is_self(s)
                        && matches!(resolve(ctx, &map, n), Ok(V::FieldRef(0)))
                        && ctx.variant.fields.len() == 1;
                    if !ok {
                        return Err(arm_err(ctx, "zfc-set fold args drift"));
                    }
                    map.insert(dest.local, V::ZfcFolded);
                    cur = *target;
                    continue;
                }

                if callee == OPTION_MAP {
                    let [recv, mk] = args.as_slice() else {
                        return Err(arm_err(ctx, "Option::map arity"));
                    };
                    if !is_local(dest, 0) {
                        return Err(arm_err(ctx, "Option::map result is not the arm return"));
                    }
                    match resolve(ctx, &map, recv)? {
                        V::ZfcFolded => {
                            // The ZFCSet wrap is one exact non-capturing
                            // closure; identity and behavior are both pinned.
                            if !operand_matches_callable(mk, ZFC_CLOSURES[0]) {
                                return Err(arm_err(ctx, "ZFCSet wrap callable identity drift"));
                            }
                            match_zst_ctor_closure(
                                pinned_callable_body(bodies, ZFC_CLOSURES[0])?,
                                22,
                                CtorWrap2::ZfcSetWrap,
                                1,
                                1,
                            )?;
                            let mut seen = std::collections::BTreeSet::new();
                            check_epilogue(ctx, *target, &mut seen)?;
                            return Ok(ArmOutcome::ZfcSetDispatch);
                        }
                        V::Folded(f) => {
                            let make = if let Some(V::Closure { name, caps }) =
                                op_local(mk).and_then(|l| map.get(&l)).cloned()
                            {
                                MakeKind::NamedClosure(name, caps)
                            } else if let Some((path, kind, hash)) = callable_const(mk) {
                                MakeKind::Callable(path.to_string(), kind, hash)
                            } else {
                                return Err(arm_err(ctx, "Option::map make drift"));
                            };
                            check_map_make(ctx, bodies, &make)?;
                            let mut seen = std::collections::BTreeSet::new();
                            check_epilogue(ctx, *target, &mut seen)?;
                            let binder = folded_binder.get(&f).copied().unwrap_or(false);
                            return Ok(ArmOutcome::Arm(TArm::Map1 { child: f, binder }));
                        }
                        other => {
                            return Err(arm_err(ctx, format!("Option::map over {other:?}")));
                        }
                    }
                }

                if callee == MERGE2_FN || callee == MERGE3_FN || callee == MERGE4_FN {
                    let k = match callee.as_str() {
                        c if c == MERGE2_FN => 2usize,
                        c if c == MERGE3_FN => 3,
                        _ => 4,
                    };
                    if args.len() != 2 * k + 1 {
                        return Err(arm_err(ctx, "merge arity drift"));
                    }
                    if !is_local(dest, 0) {
                        return Err(arm_err(ctx, "merge result is not the arm return"));
                    }
                    // olds: the variant's REC field refs, in order.
                    let recs = rec_fields(ctx.variant);
                    if recs.len() != k {
                        return Err(arm_err(
                            ctx,
                            format!("merge{k} over a variant with {} rec fields", recs.len()),
                        ));
                    }
                    let mut children = Vec::with_capacity(k);
                    for (i, old) in args[..k].iter().enumerate() {
                        let Ok(V::FieldRef(f)) = resolve(ctx, &map, old) else {
                            return Err(arm_err(
                                ctx,
                                format!("merge old-arg {i} is not a field ref"),
                            ));
                        };
                        if f != recs[i] {
                            return Err(arm_err(
                                ctx,
                                format!("merge old-arg {i} is field {f}, want {}", recs[i]),
                            ));
                        }
                        children.push(f);
                    }
                    for (i, new) in args[k..2 * k].iter().enumerate() {
                        let Ok(V::Folded(f)) = resolve(ctx, &map, new) else {
                            return Err(arm_err(
                                ctx,
                                format!("merge new-arg {i} is not a fold result"),
                            ));
                        };
                        if f != children[i] {
                            return Err(arm_err(
                                ctx,
                                format!(
                                    "merge new-arg {i} folds field {f} but old-arg is field {}",
                                    children[i]
                                ),
                            ));
                        }
                    }
                    let mk = &args[2 * k];
                    let make = if let Some(V::Closure { name, caps }) =
                        op_local(mk).and_then(|l| map.get(&l)).cloned()
                    {
                        MakeKind::NamedClosure(name, caps)
                    } else if let Some((path, kind, hash)) = callable_const(mk) {
                        MakeKind::Callable(path.to_string(), kind, hash)
                    } else {
                        return Err(arm_err(ctx, "merge make drift"));
                    };
                    check_merge_make(ctx, bodies, &make)?;
                    let mut seen = std::collections::BTreeSet::new();
                    check_epilogue(ctx, *target, &mut seen)?;
                    let binders: Vec<bool> = children
                        .iter()
                        .map(|c| folded_binder.get(c).copied().unwrap_or(false))
                        .collect();
                    return Ok(ArmOutcome::Arm(TArm::Merge { children, binders }));
                }

                // Leaf hooks.
                if let Some(rest) = callee.strip_prefix(TRAIT_PREFIX) {
                    if let Some(method) = rest.strip_prefix("::") {
                        if let Some(slot) = LeafSlot::ALL.into_iter().find(|s| s.method() == method)
                        {
                            let [s, payloads @ ..] = args.as_slice() else {
                                return Err(arm_err(ctx, "leaf call with no receiver"));
                            };
                            if !is_self(s) {
                                return Err(arm_err(ctx, "leaf call receiver is not self"));
                            }
                            if !is_local(dest, 0) {
                                return Err(arm_err(ctx, "leaf result is not the arm return"));
                            }
                            let want = payload_fields(ctx.variant);
                            if !rec_fields(ctx.variant).is_empty() {
                                return Err(arm_err(ctx, "leaf call on a recursive variant"));
                            }
                            if payloads.len() != want.len() {
                                return Err(arm_err(ctx, "leaf payload arity drift"));
                            }
                            for (i, p) in payloads.iter().enumerate() {
                                let ok = match resolve(ctx, &map, p)? {
                                    V::PayloadVal(f) | V::FieldRef(f) => f == want[i],
                                    _ => false,
                                };
                                if !ok {
                                    return Err(ExprFoldDecline::PayloadMisuse(format!(
                                        "{}::{}: leaf payload {i} is not field {}",
                                        ctx.member, ctx.variant.name, want[i]
                                    )));
                                }
                            }
                            let mut seen = std::collections::BTreeSet::new();
                            check_epilogue(ctx, *target, &mut seen)?;
                            return Ok(ArmOutcome::Arm(TArm::Leaf(slot)));
                        }
                    }
                }

                return Err(arm_err(ctx, format!("unmodeled callee {callee}")));
            }
            other => return Err(arm_err(ctx, format!("unmodeled terminator {other:?}"))),
        }
    }
}

/// The zfc inline any-some merge (Pair / Separation / Replacement): entry
/// switch on `discr(fold_a)`, cascade on `discr(fold_b)`, both-none → None,
/// any-some → map_or_else picks + variant aggregate + Some.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn walk_zfc_inline_merge(
    ctx: &WalkCtx<'_>,
    bodies: &DumpBodies,
    map: &BTreeMap<usize, V>,
    folded: &std::collections::BTreeSet<usize>,
    folded_binder: &BTreeMap<usize, bool>,
    first: usize,
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
    exhaustive: bool,
) -> R<ArmOutcome> {
    let recs = rec_fields(ctx.variant);
    let [fa, fb] = recs.as_slice() else {
        return Err(arm_err(ctx, "inline merge on a non-2-child variant"));
    };
    if first != *fa || !folded.contains(fa) || !folded.contains(fb) {
        return Err(arm_err(ctx, "inline merge does not case on the first fold"));
    }
    if !exhaustive {
        return Err(arm_err(ctx, "inline merge switch lacks the vetted flag"));
    }
    let ob = block(ctx.body, otherwise).ok_or_else(|| arm_err(ctx, "missing otherwise"))?;
    if !matches!(ob.terminator, Terminator::Unreachable) {
        return Err(arm_err(ctx, "inline merge otherwise is reachable"));
    }
    let (none_a_bb, some_bb) = match targets {
        [(0, n), (1, s)] | [(1, s), (0, n)] => (*n, *s),
        _ => return Err(arm_err(ctx, "inline merge entry targets drift")),
    };

    // none_a: `discr(fold_b)` cascade: 0 → both-none arm, 1 → the SAME some_bb.
    let nb = block(ctx.body, none_a_bb).ok_or_else(|| arm_err(ctx, "missing cascade block"))?;
    let cascade = real_stmts(&nb);
    let [
        Statement::Assign {
            place: tp,
            rvalue: Rvalue::Use(Operand::Copy(tsrc) | Operand::Move(tsrc)),
            ..
        },
        Statement::Assign { place: dp, rvalue: Rvalue::Discriminant(dsrc), .. },
    ] = cascade.as_slice()
    else {
        return Err(arm_err(ctx, "cascade block statements drift"));
    };
    // `_71 = cp _13.f1` (tuple proj → RefOf(Folded b)), `_16 = discr((*_71))`.
    let tup_ok = matches!(map.get(&tsrc.local), Some(V::Tuple(elems))
        if tsrc.projections == vec![Projection::Field(1)]
            && elems.get(1) == Some(&V::RefOf(Box::new(V::Folded(*fb)))));
    let discr_ok = dsrc.local == tp.local && dsrc.projections == vec![Projection::Deref];
    if !tup_ok || !discr_ok {
        return Err(arm_err(ctx, "cascade does not case on the second fold"));
    }
    let Terminator::SwitchInt {
        discr: cd,
        targets: ct,
        otherwise: co,
        exhaustive_enum_unreachable: ce,
        ..
    } = &nb.terminator
    else {
        return Err(arm_err(ctx, "cascade terminator drift"));
    };
    if op_local(cd) != Some(dp.local) || !ce {
        return Err(arm_err(ctx, "cascade selector drift"));
    }
    let cob = block(ctx.body, *co).ok_or_else(|| arm_err(ctx, "missing cascade otherwise"))?;
    if !matches!(cob.terminator, Terminator::Unreachable) {
        return Err(arm_err(ctx, "cascade otherwise is reachable"));
    }
    let (both_none_bb, some_bb2) = match ct.as_slice() {
        [(0, n), (1, s)] | [(1, s), (0, n)] => (*n, *s),
        _ => return Err(arm_err(ctx, "cascade targets drift")),
    };
    if some_bb2 != some_bb {
        return Err(arm_err(ctx, "any-some paths do not converge"));
    }

    // both-none arm: `_0 = None` + epilogue.
    let bn = block(ctx.body, both_none_bb).ok_or_else(|| arm_err(ctx, "missing both-none arm"))?;
    let bn_ok = matches!(real_stmts(&bn).as_slice(),
        [Statement::Assign { place, rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops), .. }]
        if is_local(place, 0) && name == OPTION_NAME && ops.is_empty());
    if !bn_ok {
        return Err(arm_err(ctx, "both-none arm does not return None"));
    }
    match &bn.terminator {
        Terminator::Goto(next) => {
            let mut seen = std::collections::BTreeSet::new();
            check_epilogue(ctx, *next, &mut seen)?;
        }
        Terminator::Return => {}
        other => return Err(arm_err(ctx, format!("both-none terminator {other:?}"))),
    }

    // some arm: pick a (map_or_else), pick b, aggregate, Some, epilogue.
    let mut picked: Vec<(usize, usize)> = Vec::new(); // (field, picked local)
    let mut cur = some_bb;
    let mut local_map: BTreeMap<usize, V> = map.clone();
    for want_field in [*fa, *fb] {
        let b = block(ctx.body, cur).ok_or_else(|| arm_err(ctx, "missing pick block"))?;
        // Statements: dropflag noise + `_x = mv <folded>` + closure aggregate.
        let mut fold_local: Option<usize> = None;
        let mut closure: Option<(usize, String, Vec<V>)> = None;
        for s in real_stmts(&b) {
            match s {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                    ..
                } if ctx.dropflags.contains(&place.local) => {}
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Move(src) | Operand::Copy(src)),
                    ..
                } if src.projections.is_empty() => {
                    if local_map.get(&src.local) == Some(&V::Folded(want_field)) {
                        fold_local = Some(place.local);
                        local_map.insert(place.local, V::Folded(want_field));
                    } else {
                        return Err(arm_err(ctx, "pick block moves an unexpected value"));
                    }
                }
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Aggregate(AggregateKind::Closure { name, .. }, ops),
                    ..
                } => {
                    let mut caps = Vec::with_capacity(ops.len());
                    for op in ops {
                        caps.push(resolve(ctx, &local_map, op)?);
                    }
                    closure = Some((place.local, name.clone(), caps));
                }
                other => return Err(arm_err(ctx, format!("pick block statement {other:?}"))),
            }
        }
        let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b.terminator
        else {
            return Err(arm_err(ctx, "pick block does not end in map_or_else"));
        };
        if callee != OPTION_MAP_OR_ELSE {
            return Err(arm_err(ctx, format!("pick callee {callee}")));
        }
        let [recv, default_fn, some_fn] = args.as_slice() else {
            return Err(arm_err(ctx, "map_or_else arity"));
        };
        let recv_ok = op_local(recv) == fold_local
            || matches!(resolve(ctx, &local_map, recv), Ok(V::Folded(f)) if f == want_field);
        if !recv_ok {
            return Err(arm_err(ctx, "pick receiver is not the fold result"));
        }
        // default: the old-clone closure capturing THIS field's ref.
        let Some((cl_local, cl_name, cl_caps)) = closure else {
            return Err(arm_err(ctx, "pick has no old-clone closure"));
        };
        if op_local(default_fn) != Some(cl_local) {
            return Err(arm_err(ctx, "pick default is not the old-clone closure"));
        }
        if cl_caps != vec![V::FieldRef(want_field)] {
            return Err(arm_err(ctx, "old-clone closure does not capture the field ref"));
        }
        match_old_clone_closure(co_member(bodies, &cl_name)?)?;
        // some-branch: the exact Arc::new function item.
        if !operand_matches_callable(some_fn, ARC_NEW_CALLABLE) {
            return Err(arm_err(ctx, "pick some-branch Arc::new identity drift"));
        }
        picked.push((want_field, dest.local));
        local_map.insert(dest.local, V::Picked(want_field));
        cur = *t;
    }

    // aggregate + Some.
    let ab = block(ctx.body, cur).ok_or_else(|| arm_err(ctx, "missing aggregate block"))?;
    let astmts = real_stmts(&ab);
    let [
        Statement::Assign {
            place: aggp,
            rvalue: Rvalue::Aggregate(AggregateKind::Adt { name: an, variant: av, .. }, aops),
            ..
        },
        Statement::Assign {
            place: somep,
            rvalue: Rvalue::Aggregate(AggregateKind::Adt { name: sn, variant: 1, .. }, sops),
            ..
        },
    ] = astmts.as_slice()
    else {
        return Err(arm_err(ctx, "inline merge aggregate block drift"));
    };
    let agg_ok = an == ZFC_SET_EXPR_NAME
        && *av == ctx.v_idx
        && aops.len() == 2
        && op_local(&aops[0]) == Some(picked[0].1)
        && op_local(&aops[1]) == Some(picked[1].1);
    if !agg_ok {
        return Err(arm_err(ctx, "inline merge rebuilds the wrong variant/children"));
    }
    let some_ok = sn == OPTION_NAME
        && is_local(somep, 0)
        && matches!(sops.as_slice(), [x] if op_local(x) == Some(aggp.local));
    if !some_ok {
        return Err(arm_err(ctx, "inline merge Some wrap drift"));
    }
    match &ab.terminator {
        Terminator::Goto(next) => {
            let mut seen = std::collections::BTreeSet::new();
            check_epilogue(ctx, *next, &mut seen)?;
        }
        Terminator::Return => {}
        other => return Err(arm_err(ctx, format!("inline merge terminator {other:?}"))),
    }

    let binders: Vec<bool> =
        [*fa, *fb].iter().map(|c| folded_binder.get(c).copied().unwrap_or(false)).collect();
    Ok(ArmOutcome::Arm(TArm::Merge { children: vec![*fa, *fb], binders }))
}

/// The `|| old.clone()` closure (merge picks / zfc picks): reads capture .0,
/// calls `Clone::clone` on it (P-CLONE Arc position), returns.
fn match_old_clone_closure(closure: &VerifiableFunction) -> R<()> {
    let m = &closure.def_path;
    let body = &closure.body;
    if body.arg_count != 1 || body.blocks.len() != 2 {
        return Err(drift(m, "old-clone closure block shape"));
    }
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: cp_,
            rvalue: Rvalue::Use(Operand::Copy(csrc) | Operand::Move(csrc)),
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(drift(m, "old-clone closure statements"));
    };
    if !(csrc.local == 1 && csrc.projections == vec![Projection::Field(0)]) {
        return Err(drift(m, "old-clone closure does not read capture .0"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(drift(m, "old-clone closure has no clone call"));
    };
    let ok = callee == CLONE_CLONE
        && matches!(args.as_slice(), [a] if op_local(a) == Some(cp_.local))
        && is_local(dest, 0);
    if !ok {
        return Err(drift(m, "old-clone closure clone-call drift"));
    }
    let b1 = block(body, *t).ok_or_else(|| drift(m, "missing return"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(drift(m, "old-clone closure does not return the clone"));
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum CallableBehavior {
    /// The exact `ExprKind::App` tuple-variant function item.
    AppCtor,
    /// A non-capturing closure whose body must match this reconstruction shape.
    Closure(CtorWrap2),
}

fn expected_merge_callable(ctx: &WalkCtx<'_>) -> Option<(CallablePin, CallableBehavior)> {
    match (ctx.member, ctx.v_idx) {
        (GEN_FOLD_EXPR_OPT_INNER_FULL, 4) => Some((APP_CTOR_CALLABLE, CallableBehavior::AppCtor)),
        (GEN_FOLD_EXPR_OPT_EXTENSIONS, 16) => {
            Some((EXTENSION_CLOSURES[0], CallableBehavior::Closure(CtorWrap2::ExprMergeDirect)))
        }
        (GEN_FOLD_EXPR_OPT_EXTENSIONS, 18..=21) => {
            let pin = EXTENSION_CLOSURES[ctx.v_idx - 16];
            Some((pin, CallableBehavior::Closure(CtorWrap2::ExprMergeDirect)))
        }
        (GEN_FOLD_EXPR_OPT_ZFC, 23..=24) => {
            let pin = ZFC_CLOSURES[ctx.v_idx - 22];
            Some((pin, CallableBehavior::Closure(CtorWrap2::ExprMergeDirect)))
        }
        _ => None,
    }
}

fn expected_map_callable(ctx: &WalkCtx<'_>) -> Option<(CallablePin, CtorWrap2)> {
    match (ctx.member, ctx.v_idx) {
        (GEN_FOLD_EXPR_OPT_INNER_FULL, 12) => Some((INNER_FULL_CLOSURE_5, CtorWrap2::ExprMapArcEk)),
        (GEN_FOLD_EXPR_OPT_EXTENSIONS, 17) => {
            Some((EXTENSION_CLOSURES[1], CtorWrap2::ExprMapArcEk))
        }
        (GEN_FOLD_ZFC_SET_EXPR_OPT, variant) => {
            ZFC_SET_CLOSURES.iter().find_map(|(expected_variant, pin)| {
                (*expected_variant == variant).then_some((*pin, CtorWrap2::ZfcMapArcDirect))
            })
        }
        _ => None,
    }
}

fn ctor_enum_for_ctx(ctx: &WalkCtx<'_>) -> &'static str {
    if ctx.member == GEN_FOLD_ZFC_SET_EXPR_OPT { ZFC_SET_EXPR_NAME } else { EXPR_KIND_NAME }
}

/// Check a `merge*` make. Capturing closures are walked against the variant
/// layout; non-capturing callbacks require their exact path/kind/hash and,
/// for closures, their exact co-member body.
fn check_merge_make(ctx: &WalkCtx<'_>, bodies: &DumpBodies, make: &MakeKind) -> R<()> {
    match make {
        MakeKind::Callable(path, kind, hash) => {
            let Some((expected, behavior)) = expected_merge_callable(ctx) else {
                return Err(arm_err(ctx, "unexpected non-capturing merge callable"));
            };
            if !callable_identity_matches(path, *kind, *hash, expected) {
                return Err(arm_err(ctx, "merge callable path/kind/hash drift"));
            }
            match behavior {
                CallableBehavior::AppCtor => Ok(()),
                CallableBehavior::Closure(wrap) => match_zst_ctor_closure(
                    pinned_callable_body(bodies, expected)?,
                    ctx.v_idx,
                    wrap,
                    rec_fields(ctx.variant).len(),
                    ctx.variant.fields.len(),
                ),
            }
        }
        MakeKind::NamedClosure(name, caps) => {
            // Captures must be the variant's payload field refs, in payload
            // order.
            let want = payload_fields(ctx.variant);
            let cap_fields: Vec<usize> = caps
                .iter()
                .map(|c| match c {
                    V::FieldRef(f) => Ok(*f),
                    other => Err(arm_err(ctx, format!("make capture {other:?}"))),
                })
                .collect::<R<_>>()?;
            if cap_fields != want {
                return Err(arm_err(ctx, "make captures are not the payload fields in order"));
            }
            match_ctor_closure(
                co_member(bodies, name)?,
                ctx.v_idx,
                ctx.variant,
                CtorWrap::MergeDirect,
                ctor_enum_for_ctx(ctx),
            )
        }
    }
}

/// Check an `Option::map` make (single-child rebuild).
fn check_map_make(ctx: &WalkCtx<'_>, bodies: &DumpBodies, make: &MakeKind) -> R<()> {
    match make {
        MakeKind::Callable(path, kind, hash) => {
            let Some((expected, wrap)) = expected_map_callable(ctx) else {
                return Err(arm_err(ctx, "unexpected non-capturing map callable"));
            };
            if !callable_identity_matches(path, *kind, *hash, expected) {
                return Err(arm_err(ctx, "map callable path/kind/hash drift"));
            }
            match_zst_ctor_closure(
                pinned_callable_body(bodies, expected)?,
                ctx.v_idx,
                wrap,
                1,
                ctx.variant.fields.len(),
            )
        }
        MakeKind::NamedClosure(name, caps) => {
            let want = payload_fields(ctx.variant);
            let cap_fields: Vec<usize> = caps
                .iter()
                .map(|c| match c {
                    V::FieldRef(f) => Ok(*f),
                    other => Err(arm_err(ctx, format!("map make capture {other:?}"))),
                })
                .collect::<R<_>>()?;
            if cap_fields != want {
                return Err(arm_err(ctx, "map make captures are not the payload fields in order"));
            }
            match_ctor_closure(
                co_member(bodies, name)?,
                ctx.v_idx,
                ctx.variant,
                CtorWrap::MapArcEk,
                ctor_enum_for_ctx(ctx),
            )
        }
    }
}

/// How a ctor closure wraps its output.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CtorWrap {
    /// merge make: params are already-`Arc` children; builds the ExprKind
    /// aggregate directly and returns it (ek applied inside merge*).
    MergeDirect,
    /// map make: single `Expr` param, `Arc::new`-wrapped, aggregate, `ek`.
    MapArcEk,
}

/// Walk a NAMED ctor closure body: verify it builds EXACTLY the expected
/// variant with payload captures passed through (cloned/copied) at their
/// field positions and the value params at the recursive positions, in order.
#[allow(clippy::too_many_lines)]
fn match_ctor_closure(
    closure: &VerifiableFunction,
    v_idx: usize,
    variant: &DumpVariant,
    wrap: CtorWrap,
    expected_enum: &str,
) -> R<()> {
    let m = &closure.def_path;
    let body = &closure.body;
    let payloads = {
        let mut v = Vec::new();
        for (i, k) in variant.fields.iter().enumerate() {
            if *k == TField::Payload {
                v.push(i);
            }
        }
        v
    };
    let recs: Vec<usize> = variant
        .fields
        .iter()
        .enumerate()
        .filter(|(_, k)| **k == TField::Rec)
        .map(|(i, _)| i)
        .collect();
    let n_params = match wrap {
        CtorWrap::MergeDirect => recs.len(),
        CtorWrap::MapArcEk => 1,
    };
    if body.arg_count != 1 + n_params {
        return Err(drift(
            m,
            format!("ctor closure arity {} (want {})", body.arg_count, 1 + n_params),
        ));
    }
    let type_named = |ty: &Ty, expected: &str| matches!(ty, Ty::Adt { name, .. } | Ty::Datatype { name, .. } if name == expected);
    let expected_return = match wrap {
        CtorWrap::MergeDirect => expected_enum,
        CtorWrap::MapArcEk => EXPR_NAME,
    };
    if !type_named(&body.return_ty, expected_return)
        || body.locals.first().is_none_or(|local| !type_named(&local.ty, expected_return))
    {
        return Err(drift(m, format!("ctor closure return type is not {expected_return}")));
    }
    if !matches!(
        body.locals.get(1).map(|local| &local.ty),
        Some(Ty::Closure { name, upvars, .. }) if name == m && upvars.len() == payloads.len()
    ) {
        return Err(drift(m, "ctor closure environment/capture type drift"));
    }
    for param in 0..n_params {
        let Some(param_ty) = body.locals.get(param + 2).map(|local| &local.ty) else {
            return Err(drift(m, "ctor closure parameter local missing"));
        };
        let ok = match wrap {
            CtorWrap::MergeDirect => crate::trustir_fold::arc_pointee_ty(param_ty)
                .is_some_and(|pointee| type_named(pointee, EXPR_NAME)),
            CtorWrap::MapArcEk => type_named(param_ty, EXPR_NAME),
        };
        if !ok {
            return Err(drift(m, format!("ctor closure parameter {param} type drift")));
        }
    }

    // Symbolic state: capture reads / clones / param moves / Arc::new.
    #[derive(Clone, PartialEq, Eq, Debug)]
    enum CV {
        CapRef(usize),   // cap index (payload order)
        CapVal(usize),   // deref-copied or cloned capture
        ParamVal(usize), // value param index (0-based among the value params)
        Arced(usize),    // Arc::new of ParamVal
    }
    let mut map: BTreeMap<usize, CV> = BTreeMap::new();
    let mut cur = BlockId(0);
    let mut agg: Option<(usize, usize, Vec<CV>)> = None; // (local, variant, operands)
    let mut ek_result: Option<usize> = None;
    let mut steps = 0usize;
    let dropflags = drop_flag_locals(body);
    let mut visited = BTreeSet::new();
    let mut defined = BTreeSet::new();
    let mut cap_value_productions = vec![0usize; payloads.len()];
    let mut arced_params = BTreeSet::new();
    let mut arc_calls = 0usize;
    let mut clone_calls = 0usize;
    let mut ek_calls = 0usize;
    let mut output_written = false;

    loop {
        steps += 1;
        if steps > 16 {
            return Err(drift(m, "ctor closure walk budget exceeded"));
        }
        if !visited.insert(cur.0) {
            return Err(drift(m, "ctor closure control-flow cycle"));
        }
        let b = block(body, cur).ok_or_else(|| drift(m, "missing ctor closure block"))?;
        for s in real_stmts(&b) {
            if output_written {
                return Err(drift(m, "statement after ctor closure output"));
            }
            match s {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                    ..
                } if dropflags.contains(&place.local) => {}
                Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                    if !defined.insert(place.local) {
                        return Err(drift(m, "ctor closure local written twice"));
                    }
                    let val = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => {
                            match p.projections.as_slice() {
                                [Projection::Field(i)] if p.local == 1 => CV::CapRef(*i),
                                [Projection::Deref] => match map.get(&p.local) {
                                    Some(CV::CapRef(i)) => {
                                        cap_value_productions[*i] += 1;
                                        CV::CapVal(*i)
                                    }
                                    other => {
                                        return Err(drift(m, format!("deref of {other:?}")));
                                    }
                                },
                                [] if p.local >= 2 && p.local < 2 + n_params => {
                                    CV::ParamVal(p.local - 2)
                                }
                                [] => match map.get(&p.local) {
                                    Some(v) => v.clone(),
                                    None => return Err(drift(m, "untracked local use")),
                                },
                                _ => return Err(drift(m, format!("unmodeled place {p:?}"))),
                            }
                        }
                        Rvalue::Aggregate(
                            AggregateKind::Adt { name, variant: w, active_field: None, .. },
                            ops,
                        ) => {
                            if name != expected_enum {
                                return Err(drift(
                                    m,
                                    format!("aggregate of {name}, want {expected_enum}"),
                                ));
                            }
                            if *w != v_idx {
                                return Err(drift(
                                    m,
                                    format!("ctor closure builds variant {w}, want {v_idx}"),
                                ));
                            }
                            let mut vals = Vec::with_capacity(ops.len());
                            for op in ops {
                                let l = op_local(op)
                                    .ok_or_else(|| drift(m, "aggregate operand is not a local"))?;
                                let v = if l >= 2 && l < 2 + n_params {
                                    CV::ParamVal(l - 2)
                                } else {
                                    map.get(&l)
                                        .cloned()
                                        .ok_or_else(|| drift(m, "aggregate operand untracked"))?
                                };
                                vals.push(v);
                            }
                            if agg.replace((place.local, *w, vals)).is_some() {
                                return Err(drift(m, "two aggregates in the ctor closure"));
                            }
                            if wrap == CtorWrap::MergeDirect {
                                if !is_local(place, 0) {
                                    return Err(drift(m, "merge-direct aggregate is not return"));
                                }
                                output_written = true;
                            } else if place.local == 0 || place.local <= body.arg_count {
                                return Err(drift(m, "map ctor aggregate destination drift"));
                            }
                            continue;
                        }
                        other => return Err(drift(m, format!("unmodeled ctor rvalue {other:?}"))),
                    };
                    map.insert(place.local, val);
                }
                other => return Err(drift(m, format!("unmodeled ctor statement {other:?}"))),
            }
        }
        match &b.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Return => break,
            Terminator::Call {
                func: callee,
                args,
                dest,
                target: Some(t),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                ..
            } if dest.projections.is_empty() => {
                if output_written || !defined.insert(dest.local) {
                    return Err(drift(m, "ctor closure call destination/output drift"));
                }
                if callee == TOTAL_CLONE || callee == CLONE_CLONE {
                    if dest.local <= body.arg_count {
                        return Err(drift(m, "clone destination aliases closure arguments"));
                    }
                    // A payload clone: arg is a capture ref (or & of one).
                    let [a] = args.as_slice() else {
                        return Err(drift(m, "clone arity in ctor closure"));
                    };
                    let l = op_local(a).ok_or_else(|| drift(m, "clone arg shape"))?;
                    let i = match map.get(&l) {
                        Some(CV::CapRef(i)) => *i,
                        _ => return Err(drift(m, "clone of a non-capture")),
                    };
                    cap_value_productions[i] += 1;
                    clone_calls += 1;
                    map.insert(dest.local, CV::CapVal(i));
                    cur = *t;
                } else if callee == ARC_NEW_CALLABLE.path {
                    if dest.local <= body.arg_count {
                        return Err(drift(m, "Arc::new destination aliases closure arguments"));
                    }
                    if wrap != CtorWrap::MapArcEk {
                        return Err(drift(m, "Arc::new in a merge-direct ctor closure"));
                    }
                    let [a] = args.as_slice() else {
                        return Err(drift(m, "Arc::new arity"));
                    };
                    let l = op_local(a).ok_or_else(|| drift(m, "Arc::new arg shape"))?;
                    let p = match map.get(&l) {
                        Some(CV::ParamVal(p)) => *p,
                        _ if l >= 2 && l < 2 + n_params => l - 2,
                        _ => return Err(drift(m, "Arc::new of a non-param")),
                    };
                    if !arced_params.insert(p) {
                        return Err(drift(m, "duplicate Arc::new for ctor parameter"));
                    }
                    arc_calls += 1;
                    map.insert(dest.local, CV::Arced(p));
                    cur = *t;
                } else if callee == EK_FN {
                    if wrap != CtorWrap::MapArcEk {
                        return Err(drift(m, "ek in a merge-direct ctor closure"));
                    }
                    let [a] = args.as_slice() else {
                        return Err(drift(m, "ek arity"));
                    };
                    let l = op_local(a).ok_or_else(|| drift(m, "ek arg shape"))?;
                    if agg.as_ref().map(|(al, _, _)| *al) != Some(l) {
                        return Err(drift(m, "ek arg is not the built aggregate"));
                    }
                    if !is_local(dest, 0) {
                        return Err(drift(m, "ek result is not the closure return"));
                    }
                    if ek_calls != 0 {
                        return Err(drift(m, "two ek calls in ctor closure"));
                    }
                    ek_calls += 1;
                    ek_result = Some(dest.local);
                    output_written = true;
                    cur = *t;
                } else {
                    return Err(drift(m, format!("unmodeled ctor closure callee {callee}")));
                }
            }
            other => return Err(drift(m, format!("unmodeled ctor closure terminator {other:?}"))),
        }
    }

    // Final shape: the aggregate exists, and (MergeDirect) it IS the return /
    // (MapArcEk) it flowed through ek into the return.
    let Some((agg_local, _, vals)) = agg else {
        return Err(drift(m, "ctor closure builds no aggregate"));
    };
    match wrap {
        CtorWrap::MergeDirect => {
            if agg_local != 0 {
                return Err(drift(m, "merge-direct aggregate is not the closure return"));
            }
        }
        CtorWrap::MapArcEk => {
            if ek_result != Some(0) {
                return Err(drift(m, "map ctor closure does not return ek(aggregate)"));
            }
        }
    }
    // Operand routing: field i ↦ CapVal(payload-order index) for payloads,
    // ParamVal/Arced(rec-order index) for recursive children.
    if vals.len() != variant.fields.len() {
        return Err(drift(m, "ctor aggregate arity drift"));
    }
    let mut pay_i = 0usize;
    let mut rec_i = 0usize;
    for (fi, kind) in variant.fields.iter().enumerate() {
        let got = &vals[fi];
        let ok = match kind {
            TField::Payload => {
                let want = CV::CapVal(pay_i);
                pay_i += 1;
                *got == want
            }
            TField::Rec => {
                let want_p = rec_i;
                rec_i += 1;
                match wrap {
                    CtorWrap::MergeDirect => *got == CV::ParamVal(want_p),
                    CtorWrap::MapArcEk => *got == CV::Arced(want_p),
                }
            }
        };
        if !ok {
            return Err(drift(m, format!("ctor aggregate field {fi} routing drift ({got:?})")));
        }
    }
    let expected_arc_calls = usize::from(wrap == CtorWrap::MapArcEk) * n_params;
    let expected_ek_calls = usize::from(wrap == CtorWrap::MapArcEk);
    if arc_calls != expected_arc_calls
        || arced_params.len() != expected_arc_calls
        || ek_calls != expected_ek_calls
        || cap_value_productions.iter().any(|count| *count != 1)
        || !output_written
    {
        return Err(drift(
            m,
            format!(
                "ctor closure production/call counts drift (clone={clone_calls}, arc={arc_calls}, ek={ek_calls})"
            ),
        ));
    }
    Ok(())
}

// ===========================================================================
// merge2/3/4 body fingerprints (the pinned rebuild combinators)
// ===========================================================================

/// Match the `mergeK` body: any-some cascade over the K `new` params' Option
/// discriminants; both/all-none → `None`; any-some → `map_or_else` picks (new
/// if some, `|| old.clone()` if none, `Arc::new` as the some-branch ZST) in
/// param order, tupled into `FnOnce::call_once(make, ·)`, `ek`-wrapped, `Some`.
#[allow(clippy::too_many_lines)]
fn match_merge_k(func: &VerifiableFunction, bodies: &DumpBodies, k: usize) -> R<()> {
    let m = &func.def_path;
    let body = &func.body;
    if body.arg_count != 2 * k + 1 {
        return Err(drift(m, format!("merge{k} arity {}", body.arg_count)));
    }
    let dropflags = drop_flag_locals(body);
    let make_local = 2 * k + 1;

    // Mini value domain.
    #[derive(Clone, PartialEq, Eq, Debug)]
    enum MV {
        OldRef(usize), // param 1..=k (index 0-based)
        NewVal(usize), // param k+1..=2k (index 0-based)
        MakeVal,
        RefOfNew(usize),
        TupleRefs(Vec<usize>),
        DiscrOfNew(usize),
        CloneClosure(usize, String), // (which new/old index, closure name)
        Picked(usize),
        TuplePicked(Vec<usize>),
        MkResult,
        EkResult,
    }
    let base = |l: usize| -> Option<MV> {
        if (1..=k).contains(&l) {
            Some(MV::OldRef(l - 1))
        } else if (k + 1..=2 * k).contains(&l) {
            Some(MV::NewVal(l - k - 1))
        } else if l == make_local {
            Some(MV::MakeVal)
        } else {
            None
        }
    };
    let mut map: BTreeMap<usize, MV> = BTreeMap::new();
    let resolve = |map: &BTreeMap<usize, MV>, op: &Operand| -> Option<MV> {
        let l = op_local(op)?;
        map.get(&l).cloned().or_else(|| base(l))
    };

    // Walk from bb0 through the cascade to the some/none arms.
    let mut cur = BlockId(0);
    let mut checked = 0usize; // how many news' discriminants checked
    let mut some_bb: Option<BlockId> = None;
    let none_join: BlockId;
    loop {
        let b = block(body, cur).ok_or_else(|| drift(m, "missing cascade block"))?;
        for s in real_stmts(&b) {
            match s {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                    ..
                } if dropflags.contains(&place.local) => {}
                Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                    let v = match rvalue {
                        Rvalue::Ref { mutable: false, place: p } if p.projections.is_empty() => {
                            match resolve(&map, &Operand::Copy(p.clone())) {
                                Some(MV::NewVal(i)) => MV::RefOfNew(i),
                                other => {
                                    return Err(drift(m, format!("cascade borrow of {other:?}")));
                                }
                            }
                        }
                        Rvalue::Aggregate(AggregateKind::Tuple, ops) => {
                            let mut idxs = Vec::with_capacity(ops.len());
                            for op in ops {
                                match resolve(&map, op) {
                                    Some(MV::RefOfNew(i)) => idxs.push(i),
                                    other => {
                                        return Err(drift(
                                            m,
                                            format!("cascade tuple of {other:?}"),
                                        ));
                                    }
                                }
                            }
                            if idxs != (0..k).collect::<Vec<_>>() {
                                return Err(drift(m, "cascade tuple is not the news in order"));
                            }
                            MV::TupleRefs(idxs)
                        }
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => {
                            match p.projections.as_slice() {
                                [Projection::Field(i)] => match map.get(&p.local) {
                                    Some(MV::TupleRefs(idxs)) if idxs.get(*i).is_some() => {
                                        MV::RefOfNew(idxs[*i])
                                    }
                                    other => {
                                        return Err(drift(m, format!("cascade proj of {other:?}")));
                                    }
                                },
                                [] => resolve(&map, &Operand::Copy(p.clone()))
                                    .ok_or_else(|| drift(m, "cascade untracked copy"))?,
                                _ => return Err(drift(m, "cascade unmodeled place")),
                            }
                        }
                        Rvalue::Discriminant(p) => {
                            let ok = p.projections == vec![Projection::Deref];
                            match (ok, map.get(&p.local)) {
                                (true, Some(MV::RefOfNew(i))) => MV::DiscrOfNew(*i),
                                other => {
                                    return Err(drift(m, format!("cascade discr of {other:?}")));
                                }
                            }
                        }
                        other => return Err(drift(m, format!("cascade rvalue {other:?}"))),
                    };
                    map.insert(place.local, v);
                }
                other => return Err(drift(m, format!("cascade statement {other:?}"))),
            }
        }
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b.terminator else {
            return Err(drift(m, "cascade terminator is not a switch"));
        };
        let Some(MV::DiscrOfNew(i)) = op_local(discr).and_then(|l| map.get(&l)).cloned() else {
            return Err(drift(m, "cascade switch on a non-new discriminant"));
        };
        if i != checked {
            return Err(drift(m, "cascade checks news out of order"));
        }
        // Targets: 0 → next cascade / none arm; 1 → the shared some arm.
        // (The dumped switch may spell it [(0,next)] + otherwise=some or
        // [(0,next),(1,some)] — accept both.)
        let (next0, some1) = match targets.as_slice() {
            [(0, n)] => (*n, *otherwise),
            [(0, n), (1, s)] | [(1, s), (0, n)] => (*n, *s),
            _ => return Err(drift(m, "cascade switch targets drift")),
        };
        match some_bb {
            None => some_bb = Some(some1),
            Some(sb) if sb == some1 => {}
            Some(_) => return Err(drift(m, "cascade some-arms do not converge")),
        }
        checked += 1;
        if checked == k {
            none_join = next0;
            break;
        }
        cur = next0;
    }
    let some_bb = some_bb.ok_or_else(|| drift(m, "no some arm"))?;

    // The all-none arm: `_0 = None` + epilogue.
    {
        let b = block(body, none_join).ok_or_else(|| drift(m, "missing none arm"))?;
        let ok = matches!(real_stmts(&b).as_slice(),
            [Statement::Assign { place, rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops), .. }]
            if is_local(place, 0) && name == OPTION_NAME && ops.is_empty());
        if !ok {
            return Err(drift(m, "merge none arm does not return None"));
        }
    }

    // The some arm: `mv make`, then per i: `mv new_i` + clone closure {old_i}
    // + map_or_else → picked_i; then tuple, call_once, ek, Some.
    let mut cur = some_bb;
    let mut make_moved: Option<usize> = None;
    let mut picked: Vec<usize> = Vec::new(); // locals, in order
    let mut mk_result: Option<usize> = None;
    let mut ek_result: Option<usize> = None;
    let mut steps = 0usize;
    loop {
        steps += 1;
        if steps > 24 {
            return Err(drift(m, "merge some-arm walk budget exceeded"));
        }
        let b = block(body, cur).ok_or_else(|| drift(m, "missing some-arm block"))?;
        let mut pending_closure: Option<(usize, String, usize)> = None; // (local, name, old idx)
        let mut pending_new: Option<(usize, usize)> = None; // (local, new idx)
        for s in real_stmts(&b) {
            match s {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                    ..
                } if dropflags.contains(&place.local) => {}
                Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                    match rvalue {
                        Rvalue::Use(Operand::Move(p) | Operand::Copy(p))
                            if p.projections.is_empty() =>
                        {
                            match map.get(&p.local).cloned().or_else(|| base(p.local)) {
                                Some(MV::MakeVal) => {
                                    make_moved = Some(place.local);
                                    map.insert(place.local, MV::MakeVal);
                                }
                                Some(MV::NewVal(i)) => {
                                    pending_new = Some((place.local, i));
                                    map.insert(place.local, MV::NewVal(i));
                                }
                                other => {
                                    return Err(drift(m, format!("some-arm move of {other:?}")));
                                }
                            }
                        }
                        Rvalue::Aggregate(AggregateKind::Closure { name, .. }, ops) => {
                            let idx = match ops.as_slice() {
                                [op] => match resolve(&map, op) {
                                    Some(MV::OldRef(i)) => i,
                                    other => {
                                        return Err(drift(
                                            m,
                                            format!("clone closure captures {other:?}"),
                                        ));
                                    }
                                },
                                _ => return Err(drift(m, "clone closure capture arity")),
                            };
                            pending_closure = Some((place.local, name.clone(), idx));
                            map.insert(place.local, MV::CloneClosure(idx, name.clone()));
                        }
                        Rvalue::Aggregate(AggregateKind::Tuple, ops) => {
                            let mut idxs = Vec::with_capacity(ops.len());
                            for op in ops {
                                match resolve(&map, op) {
                                    Some(MV::Picked(i)) => idxs.push(i),
                                    other => {
                                        return Err(drift(m, format!("picked tuple of {other:?}")));
                                    }
                                }
                            }
                            if idxs != (0..k).collect::<Vec<_>>() {
                                return Err(drift(m, "picked tuple is not in param order"));
                            }
                            map.insert(place.local, MV::TuplePicked(idxs));
                        }
                        Rvalue::Aggregate(AggregateKind::Adt { name, variant: 1, .. }, ops)
                            if name == OPTION_NAME =>
                        {
                            // `_0 = Some(ek_result)` — and it must be the FINAL
                            // real statement of its block.
                            let ok = is_local(place, 0)
                                && matches!(ops.as_slice(), [x]
                                if op_local(x).is_some_and(|l| Some(l) == ek_result));
                            if !ok {
                                return Err(drift(m, "merge Some wrap drift"));
                            }
                            {
                                let stmts = real_stmts(b);
                                if !std::ptr::eq(*stmts.last().expect("nonempty"), s) {
                                    return Err(drift(m, "statements after the merge Some write"));
                                }
                            }
                            // Epilogue.
                            match &b.terminator {
                                Terminator::Return => return Ok(()),
                                Terminator::Goto(next) => {
                                    return check_merge_epilogue(m, body, *next, &dropflags);
                                }
                                other => {
                                    return Err(drift(
                                        m,
                                        format!("merge Some terminator {other:?}"),
                                    ));
                                }
                            }
                        }
                        other => return Err(drift(m, format!("some-arm rvalue {other:?}"))),
                    }
                }
                other => return Err(drift(m, format!("some-arm statement {other:?}"))),
            }
        }
        match &b.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Call { func: callee, args, dest, target: Some(t), .. } => {
                if callee == OPTION_MAP_OR_ELSE {
                    let i = picked.len();
                    let [recv, default_fn, some_fn] = args.as_slice() else {
                        return Err(drift(m, "map_or_else arity"));
                    };
                    let recv_ok = pending_new
                        .is_some_and(|(l, ni)| op_local(recv) == Some(l) && ni == i)
                        || matches!(resolve(&map, recv), Some(MV::NewVal(ni)) if ni == i);
                    if !recv_ok {
                        return Err(drift(m, format!("pick {i} receiver drift")));
                    }
                    let cl_ok = pending_closure
                        .as_ref()
                        .is_some_and(|(l, _, ci)| op_local(default_fn) == Some(*l) && *ci == i);
                    if !cl_ok {
                        return Err(drift(m, format!("pick {i} default closure drift")));
                    }
                    if !operand_matches_callable(some_fn, ARC_NEW_CALLABLE) {
                        return Err(drift(
                            m,
                            format!("pick {i} some-branch Arc::new identity drift"),
                        ));
                    }
                    let (_, cl_name, _) = pending_closure.unwrap();
                    match_old_clone_closure(co_member(bodies, &cl_name)?)?;
                    map.insert(dest.local, MV::Picked(i));
                    picked.push(dest.local);
                    // Re-index picked by order: Picked(i) tracked positionally.
                    let l = dest.local;
                    map.insert(l, MV::Picked(i));
                    cur = *t;
                } else if callee == FNONCE_CALL_ONCE {
                    let ok = matches!(args.as_slice(), [f, tup]
                        if make_moved.is_some_and(|ml| op_local(f) == Some(ml))
                            && matches!(resolve(&map, tup), Some(MV::TuplePicked(_))));
                    if !ok {
                        return Err(drift(m, "call_once(make, picked-tuple) drift"));
                    }
                    mk_result = Some(dest.local);
                    map.insert(dest.local, MV::MkResult);
                    cur = *t;
                } else if callee == EK_FN {
                    let ok = matches!(args.as_slice(), [x]
                        if op_local(x).is_some_and(|l| Some(l) == mk_result));
                    if !ok {
                        return Err(drift(m, "merge ek arg is not the make result"));
                    }
                    ek_result = Some(dest.local);
                    map.insert(dest.local, MV::EkResult);
                    cur = *t;
                } else {
                    return Err(drift(m, format!("some-arm callee {callee}")));
                }
            }
            other => return Err(drift(m, format!("some-arm terminator {other:?}"))),
        }
    }
}

/// The merge bodies' epilogue: drop-flag switches + drops of temps → Return.
fn check_merge_epilogue(
    m: &str,
    body: &VerifiableBody,
    bb: BlockId,
    dropflags: &std::collections::BTreeSet<usize>,
) -> R<()> {
    let mut visited = std::collections::BTreeSet::new();
    let mut stack = vec![bb];
    while let Some(cur) = stack.pop() {
        if !visited.insert(cur.0) {
            continue;
        }
        let b = block(body, cur).ok_or_else(|| drift(m, "missing epilogue block"))?;
        for s in real_stmts(&b) {
            let ok = matches!(s,
                Statement::Assign { place, rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))), .. }
                if place.projections.is_empty() && dropflags.contains(&place.local));
            if !ok {
                return Err(drift(m, format!("merge epilogue statement {s:?}")));
            }
        }
        match &b.terminator {
            Terminator::Return => {}
            Terminator::Goto(next) => stack.push(*next),
            Terminator::Drop { place, target, .. } => {
                if place.local == 0 {
                    return Err(drift(m, "merge epilogue drops the return"));
                }
                stack.push(*target);
            }
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let Some(l) = op_local(discr) else {
                    return Err(drift(m, "merge epilogue switch selector"));
                };
                if !dropflags.contains(&l) {
                    return Err(drift(m, "merge epilogue switch on non-drop-flag"));
                }
                for (_, t) in targets {
                    stack.push(*t);
                }
                stack.push(*otherwise);
            }
            other => return Err(drift(m, format!("merge epilogue terminator {other:?}"))),
        }
    }
    Ok(())
}

// ===========================================================================
// Dispatch assembly — compose inner_full / extensions / zfc / fold_zfc
// ===========================================================================

/// Find a folder's override dump for `method`, trying the `<F as Trait>::m`
/// and `<F<'_> as Trait>::m` spellings.
fn override_body<'a>(
    bodies: &'a DumpBodies,
    folder: &str,
    method: &str,
) -> Option<(&'a VerifiableFunction, String)> {
    for spelled in [
        format!("<{folder} as {TRAIT_PREFIX}>::{method}"),
        format!("<{folder}<'_> as {TRAIT_PREFIX}>::{method}"),
    ] {
        if let Some(f) = bodies.get(&spelled) {
            return Some((f, spelled));
        }
    }
    None
}

/// Match one dispatch body's ENTRY (`Expr::kind` + discriminant switch) and
/// return (kind_local, tag→target map, covered tags). `require_exhaustive`:
/// inner_full/fold_zfc carry the TyCtxt-vetted flag with Unreachable
/// otherwise; extensions/zfc are partial with a DIVERGING panic otherwise.
struct DispatchEntry {
    kind_local: usize,
    targets: Vec<(i128, BlockId)>,
}

fn match_dispatch_entry(
    member: &str,
    body: &VerifiableBody,
    bodies: &DumpBodies,
    require_exhaustive: bool,
) -> R<DispatchEntry> {
    let dropflags = drop_flag_locals(body);
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(member, "no entry block"))?;
    for s in real_stmts(b0) {
        let ok = matches!(s,
            Statement::Assign { place, rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))), .. }
            if place.projections.is_empty() && dropflags.contains(&place.local));
        if !ok {
            return Err(drift(member, format!("entry statement {s:?}")));
        }
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t1), .. } = &b0.terminator else {
        return Err(drift(member, "entry does not call Expr::kind"));
    };
    if callee != EXPR_KIND_ACCESSOR {
        return Err(drift(member, format!("entry callee {callee}")));
    }
    if !matches!(args.as_slice(), [a] if op_local(a) == Some(2)) {
        return Err(drift(member, "kind arg is not the expr param"));
    }
    match_expr_kind_accessor(co_member(bodies, EXPR_KIND_ACCESSOR)?)?;
    let kind_local = dest.local;

    let b1 = block(body, *t1).ok_or_else(|| drift(member, "missing switch block"))?;
    let s1 = real_stmts(b1);
    let [Statement::Assign { place: dp, rvalue: Rvalue::Discriminant(dsrc), .. }] = s1.as_slice()
    else {
        return Err(drift(member, "switch block is not the discriminant read"));
    };
    if !(dsrc.local == kind_local && dsrc.projections == vec![Projection::Deref]) {
        return Err(drift(member, "discriminant is not of the kind ref"));
    }
    let Terminator::SwitchInt { discr, targets, otherwise, exhaustive_enum_unreachable, .. } =
        &b1.terminator
    else {
        return Err(drift(member, "no dispatch switch"));
    };
    if op_local(discr) != Some(dp.local) {
        return Err(drift(member, "switch selector drift"));
    }
    if require_exhaustive {
        if !exhaustive_enum_unreachable {
            return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                "{member}: switch lacks the TyCtxt-vetted exhaustive flag"
            )));
        }
        let ob = block(body, *otherwise).ok_or_else(|| drift(member, "missing otherwise"))?;
        if !matches!(ob.terminator, Terminator::Unreachable) {
            return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                "{member}: otherwise is reachable"
            )));
        }
    } else {
        check_diverging_panic(member, body, *otherwise)?;
    }
    let mut out = Vec::with_capacity(targets.len());
    for (tag, bb) in targets {
        let tag = i128::try_from(*tag)
            .map_err(|_| drift(member, "switch tag exceeds the modeled range"))?;
        out.push((tag, *bb));
    }
    Ok(DispatchEntry { kind_local, targets: out })
}

/// The `unreachable!()` otherwise of the partial dispatchers: a chain that
/// never assigns `_0` and ends in a DIVERGING call (panic).
fn check_diverging_panic(member: &str, body: &VerifiableBody, bb: BlockId) -> R<()> {
    let mut cur = bb;
    for _ in 0..8 {
        let b = block(body, cur).ok_or_else(|| drift(member, "missing panic block"))?;
        for s in &b.stmts {
            if let Statement::Assign { place, .. } = s {
                if place.local == 0 {
                    return Err(drift(member, "panic path assigns the return"));
                }
            }
        }
        match &b.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Call { target: None, .. } => return Ok(()),
            Terminator::Call { target: Some(t), dest, .. } => {
                if dest.local == 0 {
                    return Err(drift(member, "panic path call writes the return"));
                }
                cur = *t;
            }
            Terminator::Unreachable => return Ok(()),
            other => return Err(drift(member, format!("panic path terminator {other:?}"))),
        }
    }
    Err(drift(member, "panic path budget exceeded"))
}

/// The fold_zfc_set_expr_opt entry: a direct discriminant switch on its own
/// `&ZFCSetExpr` parameter (no kind accessor), TyCtxt-vetted + Unreachable
/// otherwise.
fn match_zfc_set_entry(member: &str, body: &VerifiableBody) -> R<Vec<(i128, BlockId)>> {
    let dropflags = drop_flag_locals(body);
    let b0 = block(body, BlockId(0)).ok_or_else(|| drift(member, "no entry block"))?;
    let mut discr_local: Option<usize> = None;
    for s in real_stmts(b0) {
        match s {
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                ..
            } if place.projections.is_empty() && dropflags.contains(&place.local) => {}
            Statement::Assign { place, rvalue: Rvalue::Discriminant(dsrc), .. }
                if place.projections.is_empty()
                    && dsrc.local == 2
                    && dsrc.projections == vec![Projection::Deref] =>
            {
                if discr_local.replace(place.local).is_some() {
                    return Err(drift(member, "two discriminant reads"));
                }
            }
            other => return Err(drift(member, format!("entry statement {other:?}"))),
        }
    }
    let Some(d) = discr_local else {
        return Err(drift(member, "no discriminant read"));
    };
    let Terminator::SwitchInt { discr, targets, otherwise, exhaustive_enum_unreachable, .. } =
        &b0.terminator
    else {
        return Err(drift(member, "no dispatch switch"));
    };
    if op_local(discr) != Some(d) || !exhaustive_enum_unreachable {
        return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
            "{member}: zfc dispatch switch is not the vetted discriminant switch"
        )));
    }
    let ob = block(body, *otherwise).ok_or_else(|| drift(member, "missing otherwise"))?;
    if !matches!(ob.terminator, Terminator::Unreachable) {
        return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
            "{member}: zfc otherwise is reachable"
        )));
    }
    let mut out = Vec::with_capacity(targets.len());
    for (tag, bb) in targets {
        let tag = i128::try_from(*tag)
            .map_err(|_| drift(member, "zfc switch tag exceeds the modeled range"))?;
        out.push((tag, *bb));
    }
    Ok(out)
}

/// Build the total tag→variant-index map (each variant exactly once).
fn tag_variant_map(
    member: &str,
    variants: &[DumpVariant],
    targets: &[(i128, BlockId)],
) -> R<Vec<(usize, BlockId)>> {
    if targets.len() != variants.len() {
        return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
            "{member}: {} switch targets for {} variants",
            targets.len(),
            variants.len()
        )));
    }
    let mut seen = vec![false; variants.len()];
    let mut out = Vec::with_capacity(targets.len());
    for (tag, bb) in targets {
        let matching: Vec<usize> = variants
            .iter()
            .enumerate()
            .filter(|(_, v)| v.discriminant == *tag)
            .map(|(i, _)| i)
            .collect();
        let [v_idx] = matching.as_slice() else {
            return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                "{member}: tag {tag} matches {} variants",
                matching.len()
            )));
        };
        if seen[*v_idx] {
            return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                "{member}: variant {v_idx} targeted twice"
            )));
        }
        seen[*v_idx] = true;
        out.push((*v_idx, *bb));
    }
    Ok(out)
}

/// Sanitize a variant name into a Clean ctor fragment.
fn sanitize(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push('_');
    }
    out
}

/// Recognize the full flattened dispatch for `folder`: the 33 `TCtor`s + leaf
/// resolutions. `depth_field`: `Some` for the rung-D depth-threading folders,
/// whose `fold_binder_body_opt` OVERRIDE is required and pinned to the
/// save/inc/call/restore shape (its def-path is returned); `None` = rung-C
/// depthless, where the override is forbidden and the GENERIC default must be
/// the checked pure delegation.
#[allow(clippy::too_many_lines)]
fn recognize_dispatch(
    bodies: &DumpBodies,
    folder: &str,
    depth_field: Option<usize>,
) -> R<(Vec<TCtor>, Vec<(LeafSlot, LeafResolution)>, Option<String>)> {
    // No dispatch-internal override may exist for this folder (else the
    // generic pinned bodies do not describe it). `fold_binder_body_opt` is
    // the ONE rung-D exception, handled below.
    for m in [
        "fold_expr_opt_inner",
        "fold_expr_opt_inner_full",
        "fold_expr_opt_extensions",
        "fold_expr_opt_zfc",
        "fold_zfc_set_expr_opt",
    ] {
        if let Some((_, path)) = override_body(bodies, folder, m) {
            return Err(ExprFoldDecline::DispatchOverridden(path));
        }
    }
    let binder_override = override_body(bodies, folder, "fold_binder_body_opt");
    let binder_body_path: Option<String> = match (depth_field, binder_override) {
        (None, Some((_, path))) => {
            // A depthless memo key with a binder-body override: the pure-`d`
            // model does not describe this folder.
            return Err(ExprFoldDecline::DispatchOverridden(path));
        }
        (None, None) => {
            // Depthless: the generic default must be the pure delegation.
            let binder_default = co_member(bodies, GEN_FOLD_BINDER_BODY_OPT)?;
            match_delegation(binder_default, GEN_FOLD_EXPR_OPT)?;
            None
        }
        (Some(df), Some((_, path))) => {
            // Rung D: the override IS the SCC co-member; pin its shape and
            // that it threads exactly the memo-key depth field.
            match_binder_body_override(co_member(bodies, &path)?, df)?;
            Some(path)
        }
        (Some(_), None) => {
            // A depth-keyed memo whose binder recursion does NOT thread the
            // depth (the generic default would fold binder bodies at the
            // same depth as the key): the memo purity story is void.
            return Err(ExprFoldDecline::MissingCoMember(format!(
                "<{folder} as {TRAIT_PREFIX}>::fold_binder_body_opt (depth-key folder without a binder-body override)"
            )));
        }
    };

    // Pinned generic co-members.
    let inner = co_member(bodies, GEN_FOLD_EXPR_OPT_INNER)?;
    match_delegation(inner, GEN_FOLD_EXPR_OPT_INNER_FULL)?;
    let inner_full = co_member(bodies, GEN_FOLD_EXPR_OPT_INNER_FULL)?;
    let extensions = co_member(bodies, GEN_FOLD_EXPR_OPT_EXTENSIONS)?;
    let zfc = co_member(bodies, GEN_FOLD_EXPR_OPT_ZFC)?;
    let fold_zfc = co_member(bodies, GEN_FOLD_ZFC_SET_EXPR_OPT)?;
    match_merge_k(co_member(bodies, MERGE2_FN)?, bodies, 2)?;
    match_merge_k(co_member(bodies, MERGE3_FN)?, bodies, 3)?;
    match_merge_k(co_member(bodies, MERGE4_FN)?, bodies, 4)?;
    match_ek(co_member(bodies, EK_FN)?)?;
    match_from_kind(co_member(bodies, EXPR_FROM_KIND)?)?;
    match_expr_clone(co_member(bodies, EXPR_CLONE)?)?;
    // The ExprKind table from inner_full's own `&Expr` parameter type.
    let expr_variants: Vec<DumpVariant> = {
        let pty = inner_full
            .body
            .locals
            .get(2)
            .map(|l| &l.ty)
            .ok_or_else(|| drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "no expr param"))?;
        let Ty::Ref { mutable: false, inner } = pty else {
            return Err(drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "expr param is not &Expr"));
        };
        let Ty::Adt { name, fields, .. } = inner.as_ref() else {
            return Err(drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "expr param pointee"));
        };
        if name != EXPR_NAME {
            return Err(drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "expr param is not expr::Expr"));
        }
        let kind_ty = fields
            .iter()
            .find(|(n, _)| n == "kind")
            .map(|(_, t)| t)
            .ok_or_else(|| drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "Expr has no kind field"))?;
        check_p_acyc_variant_table(kind_ty, EXPR_KIND_NAME)?;
        expr_kind_table(kind_ty)
            .ok_or_else(|| drift(GEN_FOLD_EXPR_OPT_INNER_FULL, "ExprKind table unexpanded"))?
    };
    // The ZFCSetExpr table from fold_zfc's own parameter.
    let zfc_variants: Vec<DumpVariant> = {
        let pty = fold_zfc
            .body
            .locals
            .get(2)
            .map(|l| &l.ty)
            .ok_or_else(|| drift(GEN_FOLD_ZFC_SET_EXPR_OPT, "no setexpr param"))?;
        let Ty::Ref { mutable: false, inner } = pty else {
            return Err(drift(GEN_FOLD_ZFC_SET_EXPR_OPT, "setexpr param is not a ref"));
        };
        check_p_acyc_variant_table(inner, ZFC_SET_EXPR_NAME)?;
        zfc_table(inner)
            .ok_or_else(|| drift(GEN_FOLD_ZFC_SET_EXPR_OPT, "ZFCSetExpr table unexpanded"))?
    };

    // inner_full entry + total tag map.
    let if_entry =
        match_dispatch_entry(GEN_FOLD_EXPR_OPT_INNER_FULL, &inner_full.body, bodies, true)?;
    let if_map = tag_variant_map(GEN_FOLD_EXPR_OPT_INNER_FULL, &expr_variants, &if_entry.targets)?;
    let if_dropflags = drop_flag_locals(&inner_full.body);

    // extensions / zfc entries (partial, panic otherwise).
    let ext_entry =
        match_dispatch_entry(GEN_FOLD_EXPR_OPT_EXTENSIONS, &extensions.body, bodies, false)?;
    let ext_dropflags = drop_flag_locals(&extensions.body);
    let zfc_entry = match_dispatch_entry(GEN_FOLD_EXPR_OPT_ZFC, &zfc.body, bodies, false)?;
    let zfc_dropflags = drop_flag_locals(&zfc.body);
    // fold_zfc entry (exhaustive over ZFCSetExpr).
    let fz_targets = match_zfc_set_entry(GEN_FOLD_ZFC_SET_EXPR_OPT, &fold_zfc.body)?;
    let fz_map = tag_variant_map(GEN_FOLD_ZFC_SET_EXPR_OPT, &zfc_variants, &fz_targets)?;
    let fz_dropflags = drop_flag_locals(&fold_zfc.body);

    // Walk every real variant through the composed dispatch.
    let mut ctors: Vec<TCtor> = Vec::with_capacity(33);
    let mut zfc_set_seen = false;
    for (v_idx, arm_bb) in &if_map {
        let variant = &expr_variants[*v_idx];
        let ctx = WalkCtx {
            member: GEN_FOLD_EXPR_OPT_INNER_FULL,
            body: &inner_full.body,
            dropflags: &if_dropflags,
            scrut: ScrutBase::KindRef(if_entry.kind_local),
            variant,
            v_idx: *v_idx,
        };
        let mut outcome = walk_arm(&ctx, bodies, *arm_bb, true, false, false)?;
        if outcome == ArmOutcome::HopExtensions {
            // Resolve in extensions under the same tag.
            let tag = variant.discriminant;
            let Some((_, ext_bb)) = ext_entry.targets.iter().find(|(t, _)| *t == tag) else {
                return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                    "extensions does not cover tag {tag}"
                )));
            };
            let ctx = WalkCtx {
                member: GEN_FOLD_EXPR_OPT_EXTENSIONS,
                body: &extensions.body,
                dropflags: &ext_dropflags,
                scrut: ScrutBase::KindRef(ext_entry.kind_local),
                variant,
                v_idx: *v_idx,
            };
            outcome = walk_arm(&ctx, bodies, *ext_bb, false, true, false)?;
        }
        if outcome == ArmOutcome::HopZfc {
            let tag = variant.discriminant;
            let Some((_, zfc_bb)) = zfc_entry.targets.iter().find(|(t, _)| *t == tag) else {
                return Err(ExprFoldDecline::UnmappedSwitchTarget(format!(
                    "zfc dispatch does not cover tag {tag}"
                )));
            };
            let ctx = WalkCtx {
                member: GEN_FOLD_EXPR_OPT_ZFC,
                body: &zfc.body,
                dropflags: &zfc_dropflags,
                scrut: ScrutBase::KindRef(zfc_entry.kind_local),
                variant,
                v_idx: *v_idx,
            };
            outcome = walk_arm(&ctx, bodies, *zfc_bb, false, false, true)?;
        }
        match outcome {
            ArmOutcome::Arm(arm) => ctors.push(TCtor {
                name: sanitize(&variant.name),
                tag: variant.discriminant,
                zfc: false,
                fields: variant.fields.clone(),
                arm,
            }),
            ArmOutcome::ZfcSetDispatch => {
                // Must be the 1-field ZFCSetExpr wrapper variant; flattened.
                if zfc_set_seen {
                    return Err(ExprFoldDecline::UnmappedSwitchTarget(
                        "two ZFCSet dispatch arms".to_string(),
                    ));
                }
                zfc_set_seen = true;
                for (z_idx, z_bb) in &fz_map {
                    let zv = &zfc_variants[*z_idx];
                    let zctx = WalkCtx {
                        member: GEN_FOLD_ZFC_SET_EXPR_OPT,
                        body: &fold_zfc.body,
                        dropflags: &fz_dropflags,
                        scrut: ScrutBase::Param2,
                        variant: zv,
                        v_idx: *z_idx,
                    };
                    let z_out = walk_arm(&zctx, bodies, *z_bb, false, false, true)?;
                    let ArmOutcome::Arm(arm) = z_out else {
                        return Err(arm_err(&zctx, "zfc sub-arm produced a hop"));
                    };
                    ctors.push(TCtor {
                        name: format!("Zfc{}", sanitize(&zv.name)),
                        tag: zv.discriminant,
                        zfc: true,
                        fields: zv.fields.clone(),
                        arm,
                    });
                }
            }
            ArmOutcome::HopExtensions | ArmOutcome::HopZfc => {
                return Err(ExprFoldDecline::UnmappedSwitchTarget(
                    "unresolved dispatch hop".to_string(),
                ));
            }
        }
    }
    if !zfc_set_seen {
        return Err(ExprFoldDecline::UnmappedSwitchTarget(
            "no ZFCSet dispatch arm found".to_string(),
        ));
    }

    // Leaf resolutions.
    let mut leaves = Vec::with_capacity(5);
    for slot in LeafSlot::ALL {
        let res = if let Some((_, path)) = override_body(bodies, folder, slot.method()) {
            LeafResolution::Override(path)
        } else {
            let default_path = format!("{TRAIT_PREFIX}::{}", slot.method());
            match_default_none(co_member(bodies, &default_path)?)?;
            LeafResolution::DefaultNone
        };
        leaves.push((slot, res));
    }

    Ok((ctors, leaves, binder_body_path))
}

/// Non-capturing ctor closure shapes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CtorWrap2 {
    /// Params are `Arc<Expr>` children; builds the ExprKind variant directly.
    ExprMergeDirect,
    /// One `Expr` param; `Arc::new` + ExprKind aggregate + `ek`.
    ExprMapArcEk,
    /// One `Expr` param; `Arc::new` + ZFCSetExpr aggregate, returned directly.
    ZfcMapArcDirect,
    /// One `ZFCSetExpr` param; `ExprKind::ZFCSet(param)` aggregate + `ek`.
    ZfcSetWrap,
}

/// Walk a NON-capturing ctor closure body: no capture reads, params routed to
/// the expected variant's fields in order.
#[allow(clippy::too_many_lines)]
fn match_zst_ctor_closure(
    closure: &VerifiableFunction,
    v_idx: usize,
    wrap: CtorWrap2,
    expected_params: usize,
    expected_fields: usize,
) -> R<()> {
    let m = &closure.def_path;
    let body = &closure.body;
    if body.arg_count != expected_params + 1 {
        return Err(drift(
            m,
            format!(
                "non-capturing ctor arg_count {} (want {})",
                body.arg_count,
                expected_params + 1
            ),
        ));
    }
    if expected_fields != expected_params {
        return Err(drift(m, "non-capturing ctor field/parameter arity mismatch"));
    }
    let type_named = |ty: &Ty, expected: &str| matches!(ty, Ty::Adt { name, .. } | Ty::Datatype { name, .. } if name == expected);
    let return_name = match wrap {
        CtorWrap2::ExprMergeDirect => EXPR_KIND_NAME,
        CtorWrap2::ExprMapArcEk | CtorWrap2::ZfcSetWrap => EXPR_NAME,
        CtorWrap2::ZfcMapArcDirect => ZFC_SET_EXPR_NAME,
    };
    if !type_named(&body.return_ty, return_name)
        || body.locals.first().is_none_or(|local| !type_named(&local.ty, return_name))
    {
        return Err(drift(m, format!("non-capturing ctor return type is not {return_name}")));
    }
    if !matches!(
        body.locals.get(1).map(|local| &local.ty),
        Some(Ty::Closure { name, upvars, .. }) if name == m && upvars.is_empty()
    ) {
        return Err(drift(m, "non-capturing ctor environment type/captures drift"));
    }
    for param in 0..expected_params {
        let Some(param_ty) = body.locals.get(param + 2).map(|local| &local.ty) else {
            return Err(drift(m, "non-capturing ctor parameter local is missing"));
        };
        let ok = match wrap {
            CtorWrap2::ExprMergeDirect => crate::trustir_fold::arc_pointee_ty(param_ty)
                .is_some_and(|pointee| type_named(pointee, EXPR_NAME)),
            CtorWrap2::ExprMapArcEk | CtorWrap2::ZfcMapArcDirect => type_named(param_ty, EXPR_NAME),
            CtorWrap2::ZfcSetWrap => type_named(param_ty, ZFC_SET_EXPR_NAME),
        };
        if !ok {
            return Err(drift(m, format!("non-capturing ctor parameter {param} type drift")));
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ZV {
        RawParam(usize),
        ArcedParam(usize),
    }
    let resolve = |map: &BTreeMap<usize, ZV>, operand: &Operand| -> Option<ZV> {
        let local = op_local(operand)?;
        if (2..2 + expected_params).contains(&local) {
            Some(ZV::RawParam(local - 2))
        } else {
            map.get(&local).copied()
        }
    };

    let mut cur = BlockId(0);
    let mut values: BTreeMap<usize, ZV> = BTreeMap::new();
    let mut defined = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut arced_params = BTreeSet::new();
    let mut aggregate: Option<usize> = None;
    let mut arc_calls = 0usize;
    let mut ek_calls = 0usize;
    let mut output_written = false;
    let mut reached_return = false;
    for _ in 0..=body.blocks.len() {
        if !visited.insert(cur.0) {
            return Err(drift(m, "non-capturing ctor control-flow cycle"));
        }
        let b = block(body, cur).ok_or_else(|| drift(m, "missing zst closure block"))?;
        for s in real_stmts(b) {
            if output_written {
                return Err(drift(m, "statement after non-capturing ctor output"));
            }
            match s {
                Statement::Assign {
                    place,
                    rvalue:
                        Rvalue::Aggregate(AggregateKind::Adt { name, variant, active_field: None, .. }, ops),
                    ..
                } if place.projections.is_empty() => {
                    if !defined.insert(place.local) {
                        return Err(drift(m, "non-capturing ctor local written twice"));
                    }
                    let expected_enum = match wrap {
                        CtorWrap2::ZfcMapArcDirect => ZFC_SET_EXPR_NAME,
                        _ => EXPR_KIND_NAME,
                    };
                    if name != expected_enum || *variant != v_idx || ops.len() != expected_fields {
                        return Err(drift(
                            m,
                            "non-capturing ctor aggregate enum/variant/arity drift",
                        ));
                    }
                    if aggregate.replace(place.local).is_some() {
                        return Err(drift(m, "two aggregates in non-capturing ctor"));
                    }
                    for (index, operand) in ops.iter().enumerate() {
                        let want = match wrap {
                            CtorWrap2::ExprMergeDirect | CtorWrap2::ZfcSetWrap => {
                                ZV::RawParam(index)
                            }
                            CtorWrap2::ExprMapArcEk | CtorWrap2::ZfcMapArcDirect => {
                                ZV::ArcedParam(index)
                            }
                        };
                        if resolve(&values, operand) != Some(want) {
                            return Err(drift(
                                m,
                                format!("non-capturing ctor aggregate field {index} routing drift"),
                            ));
                        }
                    }
                    if matches!(wrap, CtorWrap2::ExprMergeDirect | CtorWrap2::ZfcMapArcDirect) {
                        if !is_local(place, 0) {
                            return Err(drift(
                                m,
                                "direct non-capturing ctor aggregate is not return",
                            ));
                        }
                        output_written = true;
                    } else if place.local == 0 || place.local <= body.arg_count {
                        return Err(drift(m, "wrapped ctor aggregate destination drift"));
                    }
                }
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Move(p) | Operand::Copy(p)),
                    ..
                } if place.projections.is_empty() && p.projections.is_empty() => {
                    if place.local == 0
                        || place.local <= body.arg_count
                        || !defined.insert(place.local)
                    {
                        return Err(drift(m, "non-capturing ctor move destination drift"));
                    }
                    let value = if (2..2 + expected_params).contains(&p.local) {
                        ZV::RawParam(p.local - 2)
                    } else {
                        values
                            .get(&p.local)
                            .copied()
                            .ok_or_else(|| drift(m, "non-capturing ctor untracked move"))?
                    };
                    values.insert(place.local, value);
                }
                other => return Err(drift(m, format!("zst closure statement {other:?}"))),
            }
        }
        match &b.terminator {
            Terminator::Return => {
                reached_return = true;
                break;
            }
            Terminator::Goto(next) => cur = *next,
            Terminator::Call {
                func: callee,
                args,
                dest,
                target: Some(t),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                ..
            } if dest.projections.is_empty() => {
                if output_written || !defined.insert(dest.local) {
                    return Err(drift(m, "non-capturing ctor call destination/output drift"));
                }
                if callee == ARC_NEW_CALLABLE.path {
                    if dest.local <= body.arg_count {
                        return Err(drift(
                            m,
                            "Arc::new destination aliases non-capturing ctor arguments",
                        ));
                    }
                    if !matches!(wrap, CtorWrap2::ExprMapArcEk | CtorWrap2::ZfcMapArcDirect) {
                        return Err(drift(m, "unexpected Arc::new in non-Arc ctor mode"));
                    }
                    let [a] = args.as_slice() else { return Err(drift(m, "Arc::new arity")) };
                    let Some(ZV::RawParam(param)) = resolve(&values, a) else {
                        return Err(drift(m, "Arc::new of a non-param"));
                    };
                    if !arced_params.insert(param) {
                        return Err(drift(m, "duplicate Arc::new for one ctor parameter"));
                    }
                    values.insert(dest.local, ZV::ArcedParam(param));
                    arc_calls += 1;
                    cur = *t;
                } else if callee == EK_FN {
                    if !matches!(wrap, CtorWrap2::ExprMapArcEk | CtorWrap2::ZfcSetWrap) {
                        return Err(drift(m, "unexpected ek in direct non-capturing ctor"));
                    }
                    let ok = matches!(args.as_slice(), [a]
                        if op_local(a).is_some_and(|local| aggregate == Some(local)))
                        && is_local(dest, 0)
                        && ek_calls == 0;
                    if !ok {
                        return Err(drift(m, "zst ek drift"));
                    }
                    ek_calls += 1;
                    output_written = true;
                    cur = *t;
                } else {
                    return Err(drift(m, format!("zst closure callee {callee}")));
                }
            }
            other => return Err(drift(m, format!("zst closure terminator {other:?}"))),
        }
    }
    if !reached_return {
        return Err(drift(m, "non-capturing ctor never reached Return"));
    }
    if aggregate.is_none() {
        return Err(drift(m, "zst closure builds no aggregate"));
    }
    let (want_arc_calls, want_ek_calls) = match wrap {
        CtorWrap2::ExprMergeDirect | CtorWrap2::ZfcSetWrap => {
            (0, usize::from(matches!(wrap, CtorWrap2::ZfcSetWrap)))
        }
        CtorWrap2::ExprMapArcEk => (expected_params, 1),
        CtorWrap2::ZfcMapArcDirect => (expected_params, 0),
    };
    if arc_calls != want_arc_calls
        || arced_params.len() != want_arc_calls
        || ek_calls != want_ek_calls
        || !output_written
    {
        return Err(drift(m, "non-capturing ctor call-count/output drift"));
    }
    Ok(())
}

/// Whether a value can retain a pointer/reference into the folder. Scalar
/// copies of fields (depths, ids, booleans) deliberately return false: once
/// copied they cannot mutate the folder. Aggregate/reference carriers stay
/// tainted conservatively.
fn ty_can_carry_folder_alias(ty: &Ty) -> bool {
    match ty {
        Ty::Ref { .. } | Ty::RawPtr { .. } | Ty::Slice { .. } | Ty::Datatype { .. } => true,
        Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => ty_can_carry_folder_alias(elem),
        Ty::Tuple(fields) => fields.iter().any(ty_can_carry_folder_alias),
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, ty)| ty_can_carry_folder_alias(ty))
                || variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|(_, ty)| ty_can_carry_folder_alias(ty))
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(ty_can_carry_folder_alias)
        }
        // Dynamic/unsupported representations may carry a data pointer whose
        // provenance the reduced type graph cannot expose. Fail closed rather
        // than treating absent field metadata as proof of detachment.
        Ty::Dynamic { .. } | Ty::Unsupported { .. } => true,
        Ty::Bool
        | Ty::Int { .. }
        | Ty::Float { .. }
        | Ty::Bv(_)
        | Ty::Unit
        | Ty::Never
        | Ty::FnDef { .. }
        | Ty::FnPtr { .. } => false,
        _ => true,
    }
}

/// Detect semantic interior-mutability channels visible through a shared
/// reference. Runtime bookkeeping hidden inside immutable std containers
/// (Arc refcounts, collection allocation state) is not a mutation of the
/// logical payload; direct Cell/UnsafeCell/atomic/lock channels are.
fn has_exposed_interior_mutability(ty: &Ty) -> bool {
    fn suspicious_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        ["cell", "atomic", "mutex", "rwlock", "oncelock", "lazylock", "weak"]
            .iter()
            .any(|needle| lower.contains(needle))
    }

    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => false,
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            has_exposed_interior_mutability(elem)
        }
        Ty::Tuple(fields) => fields.iter().any(has_exposed_interior_mutability),
        Ty::Ref { mutable: true, .. } | Ty::RawPtr { .. } => true,
        Ty::Ref { mutable: false, inner } => has_exposed_interior_mutability(inner),
        Ty::Adt { name, fields, variants, .. } => {
            if suspicious_name(name)
                || matches!(
                    name.as_str(),
                    "std::sync::Mutex"
                        | "std::sync::RwLock"
                        | "std::sync::OnceLock"
                        | "std::sync::LazyLock"
                )
            {
                return true;
            }
            // Exact whole-graph payload fingerprints may hide allocator
            // bookkeeping but have separately pinned logical element types.
            if p_acyc_pinned_payload_type(ty) {
                return false;
            }
            if matches!(
                name.as_str(),
                "expr::Expr"
                    | "expr::kind::ExprKind"
                    | "level::Level"
                    | "name::Name"
                    | "name::NameInner"
                    | "expr::types::FVarId"
                    | "expr::types::Literal"
            ) {
                return false;
            }
            if name == "std::sync::Arc" {
                // Ignore Arc's private refcounts, but never its logical
                // pointee. A malformed/erased layout is not evidence of
                // immutability and therefore fails closed.
                return crate::trustir_fold::arc_pointee_ty(ty)
                    .map_or(true, has_exposed_interior_mutability);
            }
            fields.iter().any(|(_, field)| has_exposed_interior_mutability(field))
                || variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|(_, field)| has_exposed_interior_mutability(field))
        }
        Ty::Datatype { name, .. } => {
            if suspicious_name(name) {
                return true;
            }
            // A back-reference/compacted datatype has no inspectable field
            // graph. Only the exact immutable clean-kernel value families
            // pinned by this lane are accepted; every unknown name fails
            // closed instead of being assumed fieldless/pure.
            !matches!(
                name.as_str(),
                "expr::Expr"
                    | "expr::kind::ExprKind"
                    | "level::Level"
                    | "name::Name"
                    | "name::NameInner"
                    | "expr::types::FVarId"
                    | "expr::types::Literal"
            )
        }
        Ty::Closure { upvars, .. } => upvars.iter().any(has_exposed_interior_mutability),
        _ => true,
    }
}

/// Payloads whose external clone/equality implementation is part of the
/// lane's explicit fingerprint/std-semantics basis. An arbitrary user ADT is
/// excluded even when its visible fields look immutable: its Clone impl can
/// mutate globals or hidden state independently of those fields.
fn pinned_external_read_payload(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => true,
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            pinned_external_read_payload(elem)
        }
        Ty::Tuple(fields) => fields.iter().all(pinned_external_read_payload),
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => matches!(
            name.as_str(),
            "expr::Expr"
                | "expr::kind::ExprKind"
                | "level::Level"
                | "name::Name"
                | "name::NameInner"
                | "expr::types::FVarId"
                | "expr::types::Literal"
        ),
        _ => false,
    }
}

/// Exact shared state carriers copied out of a folder before a leaf call.
/// Their extracted representation contains allocator raw pointers, so a raw
/// recursive type walk is intentionally too conservative; the whole graph is
/// pinned instead. This HashMap is the immutable `LevelParamSubst::subst`
/// payload. Any Cell/UnsafeCell/atomic/lock/type/layout drift changes the hash.
const PINNED_FIXED_STATE_SHARED_PAYLOAD_HASHES: &[&str] =
    &["c759217cf7c58d1bef4169ee22d4d920df63dd4611d5897e3ed81edae0a76973"];

fn pinned_fixed_state_shared_payload(ty: &Ty) -> bool {
    p_acyc_type_hash(ty)
        .is_some_and(|hash| PINNED_FIXED_STATE_SHARED_PAYLOAD_HASHES.contains(&hash.as_str()))
}

fn is_detached_pinned_shared_field_copy(rv: &Rvalue, dest_ty: &Ty) -> bool {
    let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rv else {
        return false;
    };
    if place.projections.is_empty() {
        return false;
    }
    matches!(
        dest_ty,
        Ty::Ref { mutable: false, inner }
            if !has_exposed_interior_mutability(inner)
                || pinned_fixed_state_shared_payload(inner)
    )
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

fn operand_is_folder_derived(op: &Operand, aliases: &BTreeSet<usize>) -> bool {
    operand_place(op).is_some_and(|place| aliases.contains(&place.local))
}

fn rvalue_is_folder_derived(rv: &Rvalue, aliases: &BTreeSet<usize>) -> bool {
    match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            operand_is_folder_derived(op, aliases)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_is_folder_derived(a, aliases) || operand_is_folder_derived(b, aliases)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place) => aliases.contains(&place.local),
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_is_folder_derived(op, aliases)),
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|op| operand_is_folder_derived(op, aliases))
        }
        _ => false,
    }
}

/// Exact external operations admitted on a folder-derived alias, additionally
/// gated by the receiver/argument types. A generic Clone implementation is
/// NOT intrinsically pure: `Clone::clone(&Cell<_>)` may mutate interior state.
/// Every tainted operand must therefore be a shared reference whose pointee's
/// type graph exposes no interior-mutability channel.
fn pinned_read_only_folder_alias_call(
    path: &str,
    args: &[Operand],
    aliases: &BTreeSet<usize>,
    func: &VerifiableFunction,
) -> bool {
    if !matches!(path, "__trust_total_clone" | "std::clone::Clone::clone") {
        return false;
    }
    args.iter().filter(|arg| operand_is_folder_derived(arg, aliases)).all(|arg| {
        let Some(place) = operand_place(arg) else { return false };
        matches!(
            func.body.locals.get(place.local).map(|local| &local.ty),
            Some(Ty::Ref { mutable: false, inner })
                if pinned_external_read_payload(inner)
        )
    })
}

/// Alias/provenance-aware purity proof for one method/helper. `tainted_args`
/// names argument locals whose values point into the original folder. Local
/// helpers are checked recursively with the corresponding formal tainted;
/// cycles and unavailable non-pinned callees fail closed.
fn check_folder_purity_body(
    func: &VerifiableFunction,
    bodies: &DumpBodies,
    tainted_args: &BTreeSet<usize>,
    visiting: &mut BTreeSet<(String, Vec<usize>)>,
    done: &mut BTreeSet<(String, Vec<usize>)>,
) -> R<()> {
    let key = (func.def_path.clone(), tainted_args.iter().copied().collect::<Vec<_>>());
    if done.contains(&key) {
        return Ok(());
    }
    if !visiting.insert(key.clone()) {
        return Err(ExprFoldDecline::ImpureState(format!(
            "{}: folder-derived alias enters a helper-call cycle",
            func.def_path
        )));
    }

    // Conservative, CFG-independent fixed point. MIR temporaries are normally
    // SSA-shaped; unioning aliases across all assignments is stronger and
    // prevents branch/order tricks from laundering provenance.
    let mut aliases = tainted_args.clone();
    loop {
        let mut changed = false;
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    // Storing a derived reference into `_tmp.field` taints the
                    // aggregate root just as `_tmp = aggregate(alias)` does.
                    // Restricting this propagation to projection-free places
                    // lets a caller launder `&mut self` through a tuple/ADT
                    // field and later pass `_tmp` to an unproved callee.
                    if let Some(local) = func.body.locals.get(place.local) {
                        if ty_can_carry_folder_alias(&local.ty)
                            && rvalue_is_folder_derived(rvalue, &aliases)
                            && !is_detached_pinned_shared_field_copy(rvalue, &local.ty)
                        {
                            changed |= aliases.insert(place.local);
                        }
                    }
                }
            }
            if let Terminator::Call { args, dest, .. } = &block.terminator {
                if args.iter().any(|arg| operand_is_folder_derived(arg, &aliases))
                    && func
                        .body
                        .locals
                        .get(dest.local)
                        .is_some_and(|local| ty_can_carry_folder_alias(&local.ty))
                {
                    changed |= aliases.insert(dest.local);
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if aliases.contains(&place.local)
                        && (!place.projections.is_empty() || tainted_args.contains(&place.local))
                    {
                        return Err(ExprFoldDecline::ImpureState(format!(
                            "{}: write through folder-derived local _{}",
                            func.def_path, place.local
                        )));
                    }
                    match rvalue {
                        // A pointer/reference cast can erase the very type
                        // information this provenance proof relies on (for
                        // example `&mut Folder -> *mut Folder -> usize ->
                        // *mut Folder`).  Merely declining to taint the
                        // integer intermediate would let the final pointer
                        // look detached and permit a write through it.  No
                        // cast of a folder-derived value is part of the
                        // certified leaf idioms, so fail closed at the first
                        // provenance-erasing boundary.
                        Rvalue::Cast(op, _) if operand_is_folder_derived(op, &aliases) => {
                            return Err(ExprFoldDecline::ImpureState(format!(
                                "{}: cast consumes a folder-derived alias",
                                func.def_path
                            )));
                        }
                        Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(true, place)
                            if aliases.contains(&place.local) =>
                        {
                            return Err(ExprFoldDecline::ImpureState(format!(
                                "{}: mutable alias of folder-derived local _{}",
                                func.def_path, place.local
                            )));
                        }
                        Rvalue::Unsupported { operands, .. }
                            if operands
                                .iter()
                                .any(|op| operand_is_folder_derived(op, &aliases)) =>
                        {
                            return Err(ExprFoldDecline::ImpureState(format!(
                                "{}: unsupported rvalue consumes a folder-derived alias",
                                func.def_path
                            )));
                        }
                        _ => {}
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if aliases.contains(&place.local) =>
                {
                    return Err(ExprFoldDecline::ImpureState(format!(
                        "{}: discriminant/deinit through folder-derived local _{}",
                        func.def_path, place.local
                    )));
                }
                Statement::Intrinsic { args, .. }
                    if args.iter().any(|arg| operand_is_folder_derived(arg, &aliases)) =>
                {
                    return Err(ExprFoldDecline::ImpureState(format!(
                        "{}: intrinsic consumes a folder-derived alias",
                        func.def_path
                    )));
                }
                Statement::Unsupported { operands, .. }
                    if operands.iter().any(|op| operand_is_folder_derived(op, &aliases)) =>
                {
                    return Err(ExprFoldDecline::ImpureState(format!(
                        "{}: unsupported statement consumes a folder-derived alias",
                        func.def_path
                    )));
                }
                _ => {}
            }
        }

        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } => {
                if aliases.contains(&dest.local)
                    && (!dest.projections.is_empty() || tainted_args.contains(&dest.local))
                {
                    return Err(ExprFoldDecline::ImpureState(format!(
                        "{}: call writes through folder-derived destination _{}",
                        func.def_path, dest.local
                    )));
                }
                let tainted_positions = args
                    .iter()
                    .enumerate()
                    .filter_map(|(index, arg)| {
                        operand_is_folder_derived(arg, &aliases).then_some(index + 1)
                    })
                    .collect::<BTreeSet<_>>();
                if tainted_positions.is_empty() {
                    continue;
                }
                if pinned_read_only_folder_alias_call(callee, args, &aliases, func) {
                    continue;
                }
                let Some(_) = bodies.get(callee) else {
                    return Err(ExprFoldDecline::ImpureState(format!(
                        "{}: folder-derived alias escapes to unproved callee {callee}",
                        func.def_path
                    )));
                };
                let body = co_member(bodies, callee)?;
                check_folder_purity_body(body, bodies, &tainted_positions, visiting, done)?;
            }
            Terminator::Drop { place, .. } if aliases.contains(&place.local) => {
                return Err(ExprFoldDecline::ImpureState(format!(
                    "{}: drops folder-derived local _{}",
                    func.def_path, place.local
                )));
            }
            Terminator::Opaque { .. } if !aliases.is_empty() => {
                return Err(ExprFoldDecline::ImpureState(format!(
                    "{}: opaque terminator under folder-derived state",
                    func.def_path
                )));
            }
            _ => {}
        }
    }

    visiting.remove(&key);
    done.insert(key);
    Ok(())
}

/// SCC-wide fixed-state premise for G/leaf overrides, including aliases and
/// any local helper reached with folder-derived state.
fn check_leaf_purity(leaf: &VerifiableFunction, bodies: &DumpBodies) -> R<()> {
    let tainted = BTreeSet::from([1usize]);
    check_folder_purity_body(leaf, bodies, &tainted, &mut BTreeSet::new(), &mut BTreeSet::new())
}

// ===========================================================================
// Top-level recognizer entry
// ===========================================================================

/// Recognize the Expr-scale memoized fold shape of `func` (depthless rung C
/// or depth-threading rung D), fail-closed with NAMED declines. `bodies` is
/// the whole dump directory's sibling map (the SCC co-member bodies).
pub fn sem_expr_fold_shape_of(
    func: &VerifiableFunction,
    bodies: &DumpBodies,
) -> Result<SemExprFold, ExprFoldDecline> {
    if trust_vcgen::validate_function(func).is_err()
        || !crate::assignment_types::all_assignments_match(&func.body)
    {
        return Err(ExprFoldDecline::WrapperShape(
            "root fails function validation or assignment typing".to_string(),
        ));
    }
    // The row itself must be the memoized wrapper.
    let w = match_wrapper(func)?;
    // P-STACK: the trampoline's own body + the delegation closure.
    let tramp = co_member(bodies, &w.trampoline)?;
    if !crate::trustir_fold::stack_safe_body_matches(tramp) {
        return Err(ExprFoldDecline::StackSafeDrift(format!(
            "trampoline {} is not the pinned two-literal maybe_grow forwarding shape",
            w.trampoline
        )));
    }
    match_delegation_closure(co_member(bodies, &w.closure_name)?)?;
    // The memo internals (P-ADDR / P-CLONE positions). The inline idiom has
    // no `FoldMemo` bodies — its get/insert are pinned inside the wrapper
    // (P-OPT-STD) with the same key/clone discipline.
    if !w.inline {
        match_memo_get(co_member(bodies, FOLDMEMO_GET)?)?;
        match_memo_put(co_member(bodies, FOLDMEMO_PUT)?)?;
    }
    // Rung D: the depth-increment helper's own dumped body (P-SAT-ADD).
    if w.depth_field.is_some() {
        match_checked_add_u32(co_member(bodies, CHECKED_ADD_U32)?)?;
    }
    // should_descend must be an override (the G slot's implementation).
    let Some((_, sd_path)) = override_body(bodies, &w.folder, "should_descend") else {
        return Err(ExprFoldDecline::MissingCoMember(format!(
            "<{} as {TRAIT_PREFIX}>::should_descend (no override dump)",
            w.folder
        )));
    };
    check_leaf_purity(co_member(bodies, &sd_path)?, bodies)?;
    // The composed generic dispatch (+ the rung-D binder-body SCC co-member).
    let (ctors, leaves, binder_body) = recognize_dispatch(bodies, &w.folder, w.depth_field)?;
    // Depthless folders must not have binder-marked children claiming a
    // depth semantics… they MAY: the checked pure delegation makes the marks
    // semantically inert (fold_binder_body_opt = fold_expr_opt), so the
    // depthless witness soundly ignores them. Nothing to enforce here.
    // SCC-wide memo purity: no leaf override may write through the folder.
    for (_, res) in &leaves {
        if let LeafResolution::Override(path) = res {
            check_leaf_purity(co_member(bodies, path)?, bodies)?;
        }
    }
    let depth = match (w.depth_field, binder_body) {
        (Some(df), Some(bb)) => {
            Some(SemExprFoldDepth { depth_field: df, binder_body: bb, inline_memo: w.inline })
        }
        (None, None) => None,
        _ => unreachable!("recognize_dispatch enforces the depth/binder pairing"),
    };
    Ok(SemExprFold {
        folder: w.folder,
        memo_field: w.memo_field,
        depth,
        should_descend: sd_path,
        leaves,
        ctors,
    })
}

// ===========================================================================
// Kernel witness — TExpr + OptE + Lk + combinators + foldE + adequacy
// theorems + memoFoldE + memoAdequate
// ===========================================================================

/// Registered names for one witness build.
struct WitnessNames {
    texpr: String,
    ctors: Vec<String>,
    opte: String,
    lk: String,
    pick: String,
    map1: String,
    merges: [String; 3],
    fold: String,
    memo_fold: String,
}

const NS: &str = "Trust.TrustIr.ExprFold";

fn opte_ty(n: &WitnessNames) -> Expr {
    cst(&n.opte)
}
fn texpr_ty(n: &WitnessNames) -> Expr {
    cst(&n.texpr)
}
fn opte_none(n: &WitnessNames) -> Expr {
    cst(&format!("{}.none", n.opte))
}
fn opte_some(n: &WitnessNames) -> Expr {
    cst(&format!("{}.some", n.opte))
}

/// The slot telescope: (index, type-builder). Order: G, lB, lF, lS, lC, lL.
const N_SLOTS: usize = 6;
fn slot_ty(i: usize, n: &WitnessNames) -> Expr {
    match i {
        0 => Expr::pi(bd(), texpr_ty(n), cst("Bool")),
        4 => Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), opte_ty(n))),
        _ => Expr::pi(bd(), int_ty(), opte_ty(n)),
    }
}
fn leaf_slot_index(slot: LeafSlot) -> usize {
    match slot {
        LeafSlot::BVar => 1,
        LeafSlot::FVar => 2,
        LeafSlot::Sort => 3,
        LeafSlot::Const => 4,
        LeafSlot::Lit => 5,
    }
}

/// Rung D slot telescope. Order: G, dsucc, lB, lF, lS, lC, lL.
const N_SLOTS_D: usize = 7;
fn slot_ty_d(i: usize, n: &WitnessNames) -> Expr {
    match i {
        // G : TExpr → Int → Bool (should_descend consults the depth).
        0 => Expr::pi(bd(), texpr_ty(n), Expr::pi(bd(), int_ty(), cst("Bool"))),
        // dsucc : Int → Int — the ∀-quantified depth successor (pinned
        // recognizer-side to the u32-saturating increment; P-SAT-ADD).
        1 => Expr::pi(bd(), int_ty(), int_ty()),
        // Const leaf: depth → name → levels → OptE.
        5 => {
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), opte_ty(n))))
        }
        // The other leaves: depth → payload → OptE.
        _ => Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), opte_ty(n))),
    }
}
fn leaf_slot_index_d(slot: LeafSlot) -> usize {
    match slot {
        LeafSlot::BVar => 2,
        LeafSlot::FVar => 3,
        LeafSlot::Sort => 4,
        LeafSlot::Const => 5,
        LeafSlot::Lit => 6,
    }
}

/// Whether ctor child `f` is folded through `fold_binder_body_opt` (the
/// (d+1) IH slot) per the recognizer-reconstructed arm.
fn ctor_child_is_binder(ctor: &TCtor, f: usize) -> bool {
    match &ctor.arm {
        TArm::Map1 { child, binder } => *child == f && *binder,
        TArm::Merge { children, binders } => children
            .iter()
            .position(|c| *c == f)
            .and_then(|i| binders.get(i).copied())
            .unwrap_or(false),
        TArm::Leaf(_) | TArm::NoneArm => false,
    }
}

/// Register TExpr (from the recognized ctor table), OptE, Lk, and the
/// combinators; then foldE (depthless) or foldD (rung-D depth-threading).
/// Fail-closed on any kernel rejection.
fn build_expr_fold_env(ctors: &[TCtor]) -> Result<(Environment, WitnessNames), String> {
    build_expr_fold_env_impl(ctors, false)
}
fn build_expr_fold_env_d(ctors: &[TCtor]) -> Result<(Environment, WitnessNames), String> {
    build_expr_fold_env_impl(ctors, true)
}
#[allow(clippy::too_many_lines)]
fn build_expr_fold_env_impl(
    ctors: &[TCtor],
    depth: bool,
) -> Result<(Environment, WitnessNames), String> {
    let mut env = crate::trustir_anchor::trustir_env()?;
    let names = WitnessNames {
        texpr: format!("{NS}.TExpr"),
        ctors: ctors.iter().map(|c| format!("{NS}.TExpr.{}", c.name)).collect(),
        opte: format!("{NS}.OptE"),
        lk: format!("{NS}.Lk"),
        pick: format!("{NS}.pickE"),
        map1: format!("{NS}.map1E"),
        merges: [format!("{NS}.merge2E"), format!("{NS}.merge3E"), format!("{NS}.merge4E")],
        fold: format!("{NS}.{}", if depth { "foldD" } else { "foldE" }),
        memo_fold: format!("{NS}.{}", if depth { "memoFoldD" } else { "memoFoldE" }),
    };
    {
        let mut set = std::collections::BTreeSet::new();
        for c in &names.ctors {
            if !set.insert(c) {
                return Err(format!("ctor name collision after sanitization: {c}"));
            }
        }
    }

    // ---- TExpr ----
    let t_ty = || cst(&names.texpr);
    let kernel_ctors: Vec<Constructor> = ctors
        .iter()
        .zip(&names.ctors)
        .map(|(c, cname)| {
            let mut ty = t_ty();
            for k in c.fields.iter().rev() {
                let dom = match k {
                    TField::Rec => t_ty(),
                    TField::Payload => int_ty(),
                };
                ty = Expr::pi(bd(), dom, ty);
            }
            Constructor { name: Name::from_string(cname), type_: ty }
        })
        .collect();
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(&names.texpr),
            type_: Expr::type_(),
            constructors: kernel_ctors,
        }],
    })
    .map_err(|e| format!("add_inductive(TExpr): {e:?}"))?;

    // ---- OptE ----
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(&names.opte),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(&format!("{}.none", names.opte)),
                    type_: cst(&names.opte),
                },
                Constructor {
                    name: Name::from_string(&format!("{}.some", names.opte)),
                    type_: Expr::pi(bd(), t_ty(), cst(&names.opte)),
                },
            ],
        }],
    })
    .map_err(|e| format!("add_inductive(OptE): {e:?}"))?;

    // ---- Lk (the memo lookup result) ----
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(&names.lk),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(&format!("{}.miss", names.lk)),
                    type_: cst(&names.lk),
                },
                Constructor {
                    name: Name::from_string(&format!("{}.hit", names.lk)),
                    type_: Expr::pi(bd(), cst(&names.opte), cst(&names.lk)),
                },
            ],
        }],
    })
    .map_err(|e| format!("add_inductive(Lk): {e:?}"))?;

    let opte_rec = || Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
    let opte_motive = |cod: Expr| Expr::lam(bd(), cst(&names.opte), cod);
    let add_def =
        |env: &mut Environment, name: &str, ty: Expr, value: Expr| -> Result<(), String> {
            {
                let tc = TypeChecker::new(env);
                tc.check_type(&value, &ty).map_err(|e| format!("check_type({name}): {e:?}"))?;
            }
            env.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })
            .map_err(|e| format!("add_decl({name}): {e:?}"))?;
            match env.axiom_deps(&Name::from_string(name)) {
                Some(residue) if residue.is_empty() => Ok(()),
                Some(residue) => Err(format!("{name} carries axioms: {residue:?}")),
                None => Err(format!("{name} not found after add")),
            }
        };

    // ---- pickE : TExpr → OptE → TExpr := λ o n. OptE.rec (λ_.TExpr) o (λ x. x) n
    {
        let ty = Expr::pi(bd(), t_ty(), Expr::pi(bd(), cst(&names.opte), t_ty()));
        let rec = Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
        let value = Expr::lam(
            bd(),
            t_ty(),
            Expr::lam(
                bd(),
                cst(&names.opte),
                Expr::apps(
                    rec,
                    [
                        Expr::lam(bd(), cst(&names.opte), t_ty()),
                        Expr::bvar(1),                          // none → old
                        Expr::lam(bd(), t_ty(), Expr::bvar(0)), // some x → x
                        Expr::bvar(0),                          // scrutinee n
                    ],
                ),
            ),
        );
        add_def(&mut env, &names.pick, ty, value)?;
    }

    // ---- map1E : OptE → (TExpr → TExpr) → OptE
    {
        let mk_ty = Expr::pi(bd(), t_ty(), t_ty());
        let ty = Expr::pi(bd(), cst(&names.opte), Expr::pi(bd(), mk_ty.clone(), cst(&names.opte)));
        // λ n mk. OptE.rec (λ_.OptE) none (λ x. some (mk x)) n
        let value = Expr::lam(
            bd(),
            cst(&names.opte),
            Expr::lam(
                bd(),
                mk_ty,
                Expr::apps(
                    opte_rec(),
                    [
                        opte_motive(cst(&names.opte)),
                        opte_none(&names),
                        Expr::lam(
                            bd(),
                            t_ty(),
                            Expr::app(opte_some(&names), Expr::app(Expr::bvar(1), Expr::bvar(0))),
                        ),
                        Expr::bvar(1),
                    ],
                ),
            ),
        );
        add_def(&mut env, &names.map1, ty, value)?;
    }

    // ---- mergeKE (K = 2, 3, 4) ----
    // merge2E oa ob na nb mk =
    //   OptE.rec (λ_.OptE)
    //     (OptE.rec (λ_.OptE) none (λ xb. some (mk oa xb)) nb)
    //     (λ xa. some (mk xa (pickE ob nb)))
    //     na
    // merge3E/merge4E generalize: casing on n_1; the some-branch picks the
    // rest; the none-branch recurses into the same cascade on n_2… with o_1
    // fixed. Built generically below.
    for (ki, k) in [2usize, 3, 4].iter().copied().enumerate() {
        let mut mk_ty = t_ty();
        for _ in 0..k {
            mk_ty = Expr::pi(bd(), t_ty(), mk_ty);
        }
        let mut ty = Expr::pi(bd(), mk_ty.clone(), cst(&names.opte));
        for _ in 0..k {
            ty = Expr::pi(bd(), cst(&names.opte), ty);
        }
        for _ in 0..k {
            ty = Expr::pi(bd(), t_ty(), ty);
        }
        // Telescope: o_0..o_{k-1}, n_0..n_{k-1}, mk  (mk innermost).
        // bvar indices at depth 2k+1: o_i = 2k - i, n_i = k - i, mk = 0.
        let o_var = |i: usize| Expr::bvar(u32::try_from(2 * k - i).unwrap());
        let n_var = |i: usize| Expr::bvar(u32::try_from(k - i).unwrap());
        // Build the cascade: level j (0-based) cases on n_j with binders so
        // far = extra (number of λ binders opened by outer rec minors).
        // At cascade level j under `extra` extra binders:
        //   some-branch: λ x_j. some (mk c_0 … c_{k-1}) where c_i =
        //     x_j for i == j; pickE o_i n_i for i > j; f_i (already-fixed
        //     "changed" value bound at an OUTER some-binder) — never happens
        //     for i < j in THIS shape: the some-branch at level j means
        //     n_0..n_{j-1} were all none, so c_i = o_i for i < j.
        //   none-branch: recurse to level j+1 (or `none` at k).
        fn cascade(
            names: &WitnessNames,
            k: usize,
            j: usize,
            extra: u32,
            o_var: &dyn Fn(usize) -> Expr,
            n_var: &dyn Fn(usize) -> Expr,
            mk_at: &dyn Fn(u32) -> Expr,
        ) -> Expr {
            let sh = |e: Expr, _by: u32| e; // vars are computed at exact depth
            let _ = sh;
            let opte_rec =
                Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
            let t_ty = cst(&names.texpr);
            let motive = Expr::lam(bd(), cst(&names.opte), cst(&names.opte));
            let o_at = |i: usize, extra: u32| {
                // o_i at depth (2k+1 outer) + extra binders.
                let base = 2 * k - i;
                Expr::bvar(u32::try_from(base).unwrap() + extra)
            };
            let n_at = |i: usize, extra: u32| {
                let base = k - i;
                Expr::bvar(u32::try_from(base).unwrap() + extra)
            };
            let _ = (o_var, n_var);
            if j == k {
                return cst(&format!("{}.none", names.opte));
            }
            // some-branch (λ x_j at extra+1):
            let some_body = {
                let e1 = extra + 1;
                let mut args: Vec<Expr> = Vec::with_capacity(k);
                for i in 0..k {
                    if i < j {
                        args.push(o_at(i, e1));
                    } else if i == j {
                        args.push(Expr::bvar(0));
                    } else {
                        args.push(Expr::apps(cst(&names.pick), [o_at(i, e1), n_at(i, e1)]));
                    }
                }
                Expr::app(cst(&format!("{}.some", names.opte)), Expr::apps(mk_at(e1), args))
            };
            let some_branch = Expr::lam(bd(), t_ty.clone(), some_body);
            let none_branch = cascade(names, k, j + 1, extra, o_var, n_var, mk_at);
            Expr::apps(opte_rec, [motive, none_branch, some_branch, n_at(j, extra)])
        }
        let mk_at = |extra: u32| Expr::bvar(extra);
        let body = cascade(&names, k, 0, 0, &o_var, &n_var, &mk_at);
        let mut value = Expr::lam(bd(), mk_ty, body);
        for _ in 0..k {
            value = Expr::lam(bd(), cst(&names.opte), value);
        }
        for _ in 0..k {
            value = Expr::lam(bd(), t_ty(), value);
        }
        add_def(&mut env, &names.merges[ki], ty, value)?;
    }

    // ---- foldE / foldD ----
    {
        let (ty, value) =
            if depth { fold_def_d(&names, ctors, false)? } else { fold_def(&names, ctors, false)? };
        add_def(&mut env, &names.fold, ty, value)?;
    }
    // ---- memoFoldE / memoFoldD ----
    {
        let (ty, value) =
            if depth { fold_def_d(&names, ctors, true)? } else { fold_def(&names, ctors, true)? };
        add_def(&mut env, &names.memo_fold, ty, value)?;
    }

    Ok((env, names))
}

/// Render one ctor's arm value (design §3.2 step 4's model term) at binder
/// shift `s` above the minor/statement telescope.
///
/// `field(f, s)` / `ih(f, s)` / `slot(i, s)` return the TExpr/OptE/slot terms
/// for the current telescope at extra-shift `s`. `dexp` (rung D): the depth
/// term at shift `s` — when `Some`, leaf slots receive it as their FIRST
/// argument, and the caller-provided `ih` closure is responsible for
/// rendering the IH APPLIED at the right depth (`d` / `dsucc d` per the
/// ctor's binder marks). The depthless family passes `None` (binder marks
/// semantically inert per the checked pure delegation).
fn arm_expr(
    names: &WitnessNames,
    ctor: &TCtor,
    ctor_const: &Expr,
    slot: &dyn Fn(usize, u32) -> Expr,
    field: &dyn Fn(usize, u32) -> Expr,
    ih: &dyn Fn(usize, u32) -> Expr,
    dexp: Option<&dyn Fn(u32) -> Expr>,
    s: u32,
) -> Result<Expr, String> {
    let t_ty = cst(&names.texpr);
    match &ctor.arm {
        TArm::NoneArm => Ok(opte_none(names)),
        TArm::Leaf(ls) => {
            let payloads: Vec<usize> = ctor
                .fields
                .iter()
                .enumerate()
                .filter(|(_, k)| **k == TField::Payload)
                .map(|(i, _)| i)
                .collect();
            let want_arity = if *ls == LeafSlot::Const { 2 } else { 1 };
            if payloads.len() != want_arity {
                return Err(format!(
                    "leaf arm arity mismatch: {} payloads for {:?}",
                    payloads.len(),
                    ls
                ));
            }
            let mut args: Vec<Expr> = Vec::with_capacity(want_arity + 1);
            if let Some(d) = dexp {
                args.push(d(s));
            }
            args.extend(payloads.iter().map(|f| field(*f, s)));
            let slot_idx =
                if dexp.is_some() { leaf_slot_index_d(*ls) } else { leaf_slot_index(*ls) };
            Ok(Expr::apps(slot(slot_idx, s), args))
        }
        TArm::Map1 { child, binder: _ } => {
            if ctor.fields.get(*child) != Some(&TField::Rec) {
                return Err("map1 child is not a recursive field".to_string());
            }
            let mk_body = {
                let args: Vec<Expr> = ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(f, _)| if f == *child { Expr::bvar(0) } else { field(f, s + 1) })
                    .collect();
                Expr::apps(ctor_const.clone(), args)
            };
            let mk = Expr::lam(bd(), t_ty, mk_body);
            Ok(Expr::apps(cst(&names.map1), [ih(*child, s), mk]))
        }
        TArm::Merge { children, binders: _ } => {
            let k = children.len();
            if !(2..=4).contains(&k) {
                return Err(format!("merge arity {k}"));
            }
            for c in children {
                if ctor.fields.get(*c) != Some(&TField::Rec) {
                    return Err("merge child is not a recursive field".to_string());
                }
            }
            let merge = cst(&names.merges[k - 2]);
            let mut args: Vec<Expr> = Vec::with_capacity(2 * k + 1);
            for c in children {
                args.push(field(*c, s));
            }
            for c in children {
                args.push(ih(*c, s));
            }
            let ku = u32::try_from(k).map_err(|_| "merge arity overflow".to_string())?;
            let mk_body = {
                let arg_of = |f: usize| -> Expr {
                    match children.iter().position(|c| *c == f) {
                        Some(j) => Expr::bvar(ku - 1 - u32::try_from(j).unwrap_or(0)),
                        None => field(f, s + ku),
                    }
                };
                let args: Vec<Expr> = (0..ctor.fields.len()).map(arg_of).collect();
                Expr::apps(ctor_const.clone(), args)
            };
            let mut mk = mk_body;
            for _ in 0..k {
                mk = Expr::lam(bd(), cst(&names.texpr), mk);
            }
            args.push(mk);
            Ok(Expr::apps(merge, args))
        }
    }
}

/// Build the type + value of `foldE` (memo = false) or `memoFoldE`
/// (memo = true; one extra `lk : TExpr → Lk` slot after the leaf slots).
#[allow(clippy::too_many_lines)]
fn fold_def(names: &WitnessNames, ctors: &[TCtor], memo: bool) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    let lk_ty = || Expr::pi(bd(), t_ty(), cst(&names.lk));
    let extra_slots = usize::from(memo); // + lk
    let n_outer = N_SLOTS + extra_slots;

    // Type: Π slots… (lk), TExpr → OptE.
    let mut ty = Expr::pi(bd(), t_ty(), opte_ty(names));
    if memo {
        ty = Expr::pi(bd(), lk_ty(), ty);
    }
    for i in (0..N_SLOTS).rev() {
        ty = Expr::pi(bd(), slot_ty(i, names), ty);
    }

    // Value: λ slots… (lk). TExpr.rec (λ_.OptE) minors…
    let texpr_rec = Expr::const_(Name::from_string(&format!("{}.rec", names.texpr)), vec![l1()]);
    let motive = Expr::lam(bd(), t_ty(), opte_ty(names));
    let mut rec_args: Vec<Expr> = vec![motive];
    let n_outer_u = u32::try_from(n_outer).map_err(|_| "outer overflow".to_string())?;

    for (ci, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let m = ctor.fields.iter().filter(|k| **k == TField::Rec).count();
        let nm = u32::try_from(n + m).map_err(|_| "binder overflow".to_string())?;
        // Minor telescope: fields x_0..x_{n-1}, then IHs ih_0..ih_{m-1}
        // (kernel recursor layout: fields first, then IHs, in field order).
        // Under the minor telescope + s extra binders:
        //   slot i  = bvar(nm + s + (n_outer - 1 - i))
        //   x_f     = bvar(nm + s - 1 - f)  … wait: fields bound OUTERMOST:
        //   x_f     = bvar((n + m) - 1 - f + s)
        //   ih_j(f) = bvar(m - 1 - j + s)
        let slot = move |i: usize, s: u32| {
            Expr::bvar(nm + s + (n_outer_u - 1 - u32::try_from(i).unwrap_or(0)))
        };
        let field = {
            let n = n;
            let m = m;
            move |f: usize, s: u32| Expr::bvar(u32::try_from(n + m - 1 - f).unwrap_or(u32::MAX) + s)
        };
        let rec_positions: Vec<usize> = ctor
            .fields
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == TField::Rec)
            .map(|(i, _)| i)
            .collect();
        let ih = {
            let rec_positions = rec_positions.clone();
            let m = m;
            move |f: usize, s: u32| {
                let j = rec_positions.iter().position(|p| *p == f).unwrap_or(usize::MAX);
                Expr::bvar(u32::try_from(m - 1 - j).unwrap_or(u32::MAX) + s)
            }
        };
        let ctor_const = cst(&names.ctors[ci]);
        let arm = arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, None, 0)
            .map_err(|e| format!("arm({}): {e}", ctor.name))?;
        // Guarded: Bool.rec (λ_.OptE) none arm (G (ctor xs)).
        let ctor_app = {
            let args: Vec<Expr> = (0..n).map(|f| field(f, 0)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let g_app = Expr::app(slot(0, 0), ctor_app.clone());
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
        let bool_motive = Expr::lam(bd(), cst("Bool"), opte_ty(names));
        let guarded = Expr::apps(bool_rec, [bool_motive, opte_none(names), arm, g_app]);
        // memoFoldE: wrap in the Lk.rec match on `lk (ctor xs)`.
        let minor_body = if memo {
            let lk_var = slot_like_lk(nm, 0);
            let lk_app = Expr::app(lk_var, ctor_app);
            let lk_rec = Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![l1()]);
            let lk_motive = Expr::lam(bd(), cst(&names.lk), opte_ty(names));
            let hit_fn = Expr::lam(bd(), opte_ty(names), Expr::bvar(0));
            Expr::apps(lk_rec, [lk_motive, guarded, hit_fn, lk_app])
        } else {
            guarded
        };
        // Wrap the minor telescope: IHs innermost.
        let mut minor = minor_body;
        for _ in 0..m {
            minor = Expr::lam(bd(), opte_ty(names), minor);
        }
        for k in ctor.fields.iter().rev() {
            let dom = match k {
                TField::Rec => t_ty(),
                TField::Payload => int_ty(),
            };
            minor = Expr::lam(bd(), dom, minor);
        }
        rec_args.push(minor);
    }

    let mut value = Expr::apps(texpr_rec, rec_args);
    if memo {
        value = Expr::lam(bd(), lk_ty(), value);
    }
    for i in (0..N_SLOTS).rev() {
        value = Expr::lam(bd(), slot_ty(i, names), value);
    }
    Ok((ty, value))
}

/// The `lk` binder inside a memoFoldE minor: bound right after the 6 slots,
/// so at (minor-telescope size nm + s) extra depth it is bvar(nm + s + 0).
fn slot_like_lk(nm: u32, s: u32) -> Expr {
    Expr::bvar(nm + s)
}

/// RUNG D — build the type + value of `foldD` (memo = false) or `memoFoldD`
/// (memo = true; one extra `lk : TExpr → Int → Lk` slot after the leaf
/// slots). The interpreter threads the depth FUNCTIONALLY: motive
/// `λ_. Int → OptE`, every minor `λ fields ihs. λ d. …`, IHs applied at `d`
/// or `dsucc d` per the ctor's binder marks, leaf slots receive `d` first
/// (design §3.1's `fold_binder_body_opt = λ e d. foldD … e (dsucc d)`).
#[allow(clippy::too_many_lines)]
fn fold_def_d(names: &WitnessNames, ctors: &[TCtor], memo: bool) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    // lk : TExpr → Int → Lk.
    let lk_ty = || Expr::pi(bd(), t_ty(), Expr::pi(bd(), int_ty(), cst(&names.lk)));
    let extra_slots = usize::from(memo);
    let n_outer = N_SLOTS_D + extra_slots;

    // Type: Π slots… (lk), TExpr → Int → OptE.
    let mut ty = Expr::pi(bd(), t_ty(), Expr::pi(bd(), int_ty(), opte_ty(names)));
    if memo {
        ty = Expr::pi(bd(), lk_ty(), ty);
    }
    for i in (0..N_SLOTS_D).rev() {
        ty = Expr::pi(bd(), slot_ty_d(i, names), ty);
    }

    // Value: λ slots… (lk). TExpr.rec (λ_. Int → OptE) minors…
    let texpr_rec = Expr::const_(Name::from_string(&format!("{}.rec", names.texpr)), vec![l1()]);
    let motive = Expr::lam(bd(), t_ty(), Expr::pi(bd(), int_ty(), opte_ty(names)));
    let mut rec_args: Vec<Expr> = vec![motive];
    let n_outer_u = u32::try_from(n_outer).map_err(|_| "outer overflow".to_string())?;

    for (ci, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let m = ctor.fields.iter().filter(|k| **k == TField::Rec).count();
        let nm = u32::try_from(n + m).map_err(|_| "binder overflow".to_string())?;
        // Minor telescope: fields(n), IHs(m) [each Int → OptE], then λ(d:Int).
        // Inside the λd body at `s` extra binders (s counts binders above d):
        //   d       = bvar(s)
        //   slot i  = bvar(nm + 1 + s + (n_outer − 1 − i))
        //   lk      = bvar(nm + 1 + s)               (memo only)
        //   x_f     = bvar((n + m − 1 − f) + 1 + s)
        //   ih_j    = bvar((m − 1 − j) + 1 + s)
        let slot = move |i: usize, s: u32| {
            Expr::bvar(nm + 1 + s + (n_outer_u - 1 - u32::try_from(i).unwrap_or(0)))
        };
        let dvar = |s: u32| Expr::bvar(s);
        let field = {
            move |f: usize, s: u32| {
                Expr::bvar(u32::try_from(n + m - 1 - f).unwrap_or(u32::MAX) + 1 + s)
            }
        };
        let rec_positions: Vec<usize> = ctor
            .fields
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == TField::Rec)
            .map(|(i, _)| i)
            .collect();
        // The IH applied at the child's depth: `ih_j d` or `ih_j (dsucc d)`.
        let ih = {
            let rec_positions = rec_positions.clone();
            move |f: usize, s: u32| {
                let j = rec_positions.iter().position(|p| *p == f).unwrap_or(usize::MAX);
                let ihv = Expr::bvar(u32::try_from(m - 1 - j).unwrap_or(u32::MAX) + 1 + s);
                let dd = if ctor_child_is_binder(ctor, f) {
                    Expr::app(slot(1, s), dvar(s))
                } else {
                    dvar(s)
                };
                Expr::app(ihv, dd)
            }
        };
        let ctor_const = cst(&names.ctors[ci]);
        let dexp = |s: u32| Expr::bvar(s);
        let arm = arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, Some(&dexp), 0)
            .map_err(|e| format!("arm_d({}): {e}", ctor.name))?;
        // Guarded: Bool.rec (λ_.OptE) none arm (G (ctor xs) d).
        let ctor_app = {
            let args: Vec<Expr> = (0..n).map(|f| field(f, 0)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let g_app = Expr::apps(slot(0, 0), [ctor_app.clone(), dvar(0)]);
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
        let bool_motive = Expr::lam(bd(), cst("Bool"), opte_ty(names));
        let guarded = Expr::apps(bool_rec, [bool_motive, opte_none(names), arm, g_app]);
        // memoFoldD: wrap in the Lk.rec match on `lk (ctor xs) d`.
        let minor_d_body = if memo {
            let lk_var = Expr::bvar(nm + 1);
            let lk_app = Expr::apps(lk_var, [ctor_app, dvar(0)]);
            let lk_rec = Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![l1()]);
            let lk_motive = Expr::lam(bd(), cst(&names.lk), opte_ty(names));
            let hit_fn = Expr::lam(bd(), opte_ty(names), Expr::bvar(0));
            Expr::apps(lk_rec, [lk_motive, guarded, hit_fn, lk_app])
        } else {
            guarded
        };
        // λ(d:Int). body, then the minor telescope: IHs innermost.
        let mut minor = Expr::lam(bd(), int_ty(), minor_d_body);
        for _ in 0..m {
            minor = Expr::lam(bd(), Expr::pi(bd(), int_ty(), opte_ty(names)), minor);
        }
        for k in ctor.fields.iter().rev() {
            let dom = match k {
                TField::Rec => t_ty(),
                TField::Payload => int_ty(),
            };
            minor = Expr::lam(bd(), dom, minor);
        }
        rec_args.push(minor);
    }

    let mut value = Expr::apps(texpr_rec, rec_args);
    if memo {
        value = Expr::lam(bd(), lk_ty(), value);
    }
    for i in (0..N_SLOTS_D).rev() {
        value = Expr::lam(bd(), slot_ty_d(i, names), value);
    }
    Ok((ty, value))
}

// ===========================================================================
// The adequacy theorems + memoAdequate + the cached verdict
// ===========================================================================

/// Render the HONEST guard-true RHS of ctor `i` at the STATEMENT telescope
/// (slots(6) + fields(n) + the guard hypothesis binder): the
/// recognizer-reconstructed `mergeKE/map1E/leaf/none` term with IH slots as
/// `foldE slots x_f` applications. Public probe surface (fixture tests build
/// a MUTATED ctor table, render ITS arm here, and claim it against the honest
/// witness — must be `KernelRejected`). A pure renderer; exposes no
/// acceptance path.
#[must_use]
pub fn probe_arm_rhs(ctors: &[TCtor], i: usize) -> Option<Expr> {
    let names = witness_names(ctors);
    let ctor = ctors.get(i)?;
    let n = ctor.fields.len();
    statement_rhs(&names, ctor, &names.ctors.get(i)?.clone(), n, 1).ok()
}

fn witness_names(ctors: &[TCtor]) -> WitnessNames {
    WitnessNames {
        texpr: format!("{NS}.TExpr"),
        ctors: ctors.iter().map(|c| format!("{NS}.TExpr.{}", c.name)).collect(),
        opte: format!("{NS}.OptE"),
        lk: format!("{NS}.Lk"),
        pick: format!("{NS}.pickE"),
        map1: format!("{NS}.map1E"),
        merges: [format!("{NS}.merge2E"), format!("{NS}.merge3E"), format!("{NS}.merge4E")],
        fold: format!("{NS}.foldE"),
        memo_fold: format!("{NS}.memoFoldE"),
    }
}

fn witness_names_d(ctors: &[TCtor]) -> WitnessNames {
    let mut n = witness_names(ctors);
    n.fold = format!("{NS}.foldD");
    n.memo_fold = format!("{NS}.memoFoldD");
    n
}

/// Statement-telescope accessors: slots bound first (6), then n fields, then
/// `s` extra binders (hypothesis, congr-lambda, mk-lambdas…).
fn st_slot(n: usize, i: usize, s: u32) -> Expr {
    Expr::bvar(u32::try_from(n).unwrap_or(0) + s + u32::try_from(N_SLOTS - 1 - i).unwrap_or(0))
}
fn st_field(n: usize, f: usize, s: u32) -> Expr {
    Expr::bvar(u32::try_from(n - 1 - f).unwrap_or(u32::MAX) + s)
}
fn st_fold_app(names: &WitnessNames, n: usize, e: Expr, s: u32) -> Expr {
    let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| st_slot(n, i, s)).collect();
    args.push(e);
    Expr::apps(cst(&names.fold), args)
}

/// The honest RHS at the statement telescope with `s` binders above the
/// fields.
fn statement_rhs(
    names: &WitnessNames,
    ctor: &TCtor,
    ctor_name: &str,
    n: usize,
    s: u32,
) -> Result<Expr, String> {
    let ctor_const = cst(ctor_name);
    let slot = move |i: usize, s: u32| st_slot(n, i, s);
    let field = move |f: usize, s: u32| st_field(n, f, s);
    let ih = {
        let names2 = witness_names_clone(names);
        move |f: usize, s: u32| st_fold_app(&names2, n, st_field(n, f, s), s)
    };
    arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, None, s)
}

// ---------------------------------------------------------------------------
// RUNG D statement-telescope accessors: slots(7), fields(n), d(Int), then `s`
// extra binders ABOVE d (hypothesis = 1, congr-lambda = 2, mk-lambdas…).
// ---------------------------------------------------------------------------
fn st_slot_d(n: usize, i: usize, s: u32) -> Expr {
    Expr::bvar(
        u32::try_from(n).unwrap_or(0) + 1 + s + u32::try_from(N_SLOTS_D - 1 - i).unwrap_or(0),
    )
}
fn st_field_d(n: usize, f: usize, s: u32) -> Expr {
    Expr::bvar(u32::try_from(n - 1 - f).unwrap_or(u32::MAX) + 1 + s)
}
fn st_dvar(s: u32) -> Expr {
    Expr::bvar(s)
}
/// `foldD slots e dd` at the depth-statement telescope.
fn st_fold_app_d(names: &WitnessNames, n: usize, e: Expr, dd: Expr, s: u32) -> Expr {
    let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| st_slot_d(n, i, s)).collect();
    args.push(e);
    args.push(dd);
    Expr::apps(cst(&names.fold), args)
}
/// The child depth at the statement telescope: `d` or `dsucc d`.
fn st_child_depth(ctor: &TCtor, f: usize, n: usize, s: u32) -> Expr {
    if ctor_child_is_binder(ctor, f) {
        Expr::app(st_slot_d(n, 1, s), st_dvar(s))
    } else {
        st_dvar(s)
    }
}

/// The honest DEPTH-FAMILY RHS at the statement telescope with `s` binders
/// above the depth binder.
fn statement_rhs_d(
    names: &WitnessNames,
    ctor: &TCtor,
    ctor_name: &str,
    n: usize,
    s: u32,
) -> Result<Expr, String> {
    let ctor_const = cst(ctor_name);
    let slot = move |i: usize, s: u32| st_slot_d(n, i, s);
    let field = move |f: usize, s: u32| st_field_d(n, f, s);
    let dexp = move |s: u32| st_dvar(s);
    let ih = {
        let names2 = witness_names_clone(names);
        let ctor2 = ctor.clone();
        move |f: usize, s2: u32| {
            st_fold_app_d(&names2, n, st_field_d(n, f, s2), st_child_depth(&ctor2, f, n, s2), s2)
        }
    };
    arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, Some(&dexp), s)
}

/// Depth-family probe renderer (see [`probe_arm_rhs`]): the guard-true RHS of
/// ctor `i` at the depth statement telescope — used by the forgery probes
/// (mutated binder marks / children → `KernelRejected`). A pure renderer.
#[must_use]
pub fn probe_arm_rhs_d(ctors: &[TCtor], i: usize) -> Option<Expr> {
    let names = witness_names_d(ctors);
    let ctor = ctors.get(i)?;
    let n = ctor.fields.len();
    statement_rhs_d(&names, ctor, &names.ctors.get(i)?.clone(), n, 1).ok()
}

fn witness_names_clone(n: &WitnessNames) -> WitnessNames {
    WitnessNames {
        texpr: n.texpr.clone(),
        ctors: n.ctors.clone(),
        opte: n.opte.clone(),
        lk: n.lk.clone(),
        pick: n.pick.clone(),
        map1: n.map1.clone(),
        merges: n.merges.clone(),
        fold: n.fold.clone(),
        memo_fold: n.memo_fold.clone(),
    }
}

fn eq_const() -> Expr {
    Expr::const_(Name::from_string("Eq"), vec![l1()])
}
fn eq_refl(ty: Expr, val: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1()]), [ty, val])
}

/// Check the Expr-fold refinement for a recognized ctor table: register the
/// mirror + interpreter (kernel-checked totality), prove per-ctor guard-true
/// adequacy + guard-false theorems, and the `memoAdequate` theorem. `claims`
/// overrides the guard-TRUE RHS per ctor (the FAIL-CLOSED PROBE mechanism —
/// exactly `trustir_fold::check_structural_fold_refinement_claimed`'s
/// contract: the `Eq.refl`/`congrArg` proof's ACTUAL type is pinned to the
/// honest reduct, so a claimed RHS not def-eq to it is `KernelRejected`).
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn check_expr_fold_refinement_claimed(
    ctors: &[TCtor],
    claims: &[Option<Expr>],
) -> RefinementVerdict {
    let (mut env, names) = match build_expr_fold_env(ctors) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let t_ty = || cst(&names.texpr);
    let mut residue_names: Vec<String> = Vec::new();

    for (i, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let ctor_const = cst(&names.ctors[i]);
        // ctor applied to the field binders at shift s.
        let ctor_app = |s: u32| -> Expr {
            let args: Vec<Expr> = (0..n).map(|f| st_field(n, f, s)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let g_app = |s: u32| Expr::app(st_slot(n, 0, s), ctor_app(s));

        // Wrap statement/proof in the shared Π/λ telescope: slots + fields.
        let wrap = |mut e: Expr, pi: bool| -> Expr {
            for k in ctor.fields.iter().rev() {
                let dom = match k {
                    TField::Rec => t_ty(),
                    TField::Payload => int_ty(),
                };
                e = if pi { Expr::pi(bd(), dom, e) } else { Expr::lam(bd(), dom, e) };
            }
            for si in (0..N_SLOTS).rev() {
                let d = slot_ty(si, &names);
                e = if pi { Expr::pi(bd(), d, e) } else { Expr::lam(bd(), d, e) };
            }
            e
        };

        for polarity in [true, false] {
            let bool_lit = cst(if polarity { "Bool.true" } else { "Bool.false" });
            // Hypothesis: Eq Bool (G (C xs)) <polarity>.
            let hyp = Expr::apps(eq_const(), [cst("Bool"), g_app(0), bool_lit.clone()]);
            // RHS under the hypothesis binder (s = 1).
            let honest_rhs = if polarity {
                match statement_rhs(&names, ctor, &names.ctors[i], n, 1) {
                    Ok(e) => e,
                    Err(e) => {
                        return RefinementVerdict::KernelRejected(format!(
                            "rhs({}): {e}",
                            ctor.name
                        ));
                    }
                }
            } else {
                opte_none(&names)
            };
            let rhs = if polarity {
                claims.get(i).and_then(Option::as_ref).cloned().unwrap_or(honest_rhs)
            } else {
                honest_rhs
            };
            let lhs = st_fold_app(&names, n, ctor_app(1), 1);
            let eq = Expr::apps(eq_const(), [opte_ty(&names), lhs, rhs]);
            let statement = wrap(Expr::pi(bd(), hyp.clone(), eq), true);

            // Proof: congrArg (λ b. Bool.rec (λ_.OptE) none <honest arm @ s=2> b) h.
            let f_lam = {
                let arm = if polarity {
                    match statement_rhs(&names, ctor, &names.ctors[i], n, 2) {
                        Ok(e) => e,
                        Err(e) => {
                            return RefinementVerdict::KernelRejected(format!(
                                "proof-arm({}): {e}",
                                ctor.name
                            ));
                        }
                    }
                } else {
                    // The guard-false transport uses the SAME honest reduct
                    // shape (arm in the true minor), so render the honest arm.
                    match statement_rhs(&names, ctor, &names.ctors[i], n, 2) {
                        Ok(e) => e,
                        Err(e) => {
                            return RefinementVerdict::KernelRejected(format!(
                                "proof-arm({}): {e}",
                                ctor.name
                            ));
                        }
                    }
                };
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
                let motive = Expr::lam(bd(), cst("Bool"), opte_ty(&names));
                Expr::lam(
                    bd(),
                    cst("Bool"),
                    Expr::apps(bool_rec, [motive, opte_none(&names), arm, Expr::bvar(0)]),
                )
            };
            let congr = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
                [cst("Bool"), opte_ty(&names), g_app(1), bool_lit, f_lam, Expr::bvar(0)],
            );
            let proof = wrap(Expr::lam(bd(), hyp, congr), false);

            {
                let tc = TypeChecker::new(&env);
                if let Err(e) = tc.check_type(&proof, &statement) {
                    return RefinementVerdict::KernelRejected(format!(
                        "check_type[{} {}]: {e:?}",
                        ctor.name,
                        if polarity { "guard-true" } else { "guard-false" }
                    ));
                }
            }
            let decl_name = Name::from_string(&format!(
                "Trust.TrustIr.Refinement.expr_fold_arm{i}_{}_{}",
                ctor.name,
                if polarity { "gtrue" } else { "gfalse" }
            ));
            if let Err(e) = env.add_decl(Declaration::Theorem {
                name: decl_name.clone(),
                level_params: vec![],
                type_: statement,
                value: proof,
            }) {
                return RefinementVerdict::KernelRejected(format!(
                    "add_decl[{}]: {e:?}",
                    ctor.name
                ));
            }
            match env.axiom_deps(&decl_name) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
                None => {
                    return RefinementVerdict::KernelRejected(format!(
                        "decl not found after add: {}",
                        ctor.name
                    ));
                }
            }
        }
    }

    // memoAdequate — the conditional memo-adequacy theorem (design §2
    // structure 1); P-ADDR lives in its HYPOTHESIS.
    match build_memo_adequate(&names, ctors) {
        Ok((statement, proof)) => {
            {
                let tc = TypeChecker::new(&env);
                if let Err(e) = tc.check_type(&proof, &statement) {
                    return RefinementVerdict::KernelRejected(format!(
                        "check_type[memoAdequate]: {e:?}"
                    ));
                }
            }
            let decl_name = Name::from_string(&format!("{NS}.memoAdequate"));
            if let Err(e) = env.add_decl(Declaration::Theorem {
                name: decl_name.clone(),
                level_params: vec![],
                type_: statement,
                value: proof,
            }) {
                return RefinementVerdict::KernelRejected(format!("add_decl[memoAdequate]: {e:?}"));
            }
            match env.axiom_deps(&decl_name) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
                None => {
                    return RefinementVerdict::KernelRejected(
                        "memoAdequate not found after add".to_string(),
                    );
                }
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("memoAdequate: {e}")),
    }

    if residue_names.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue_names.sort();
        residue_names.dedup();
        RefinementVerdict::Residue(residue_names)
    }
}

/// The honest (no-claims) check.
#[must_use]
pub fn check_expr_fold_refinement(ctors: &[TCtor]) -> RefinementVerdict {
    check_expr_fold_refinement_claimed(ctors, &[])
}

/// RUNG D — check the DEPTH-FAMILY Expr-fold refinement: register the mirror
/// + the depth-threading interpreter `foldD`/`memoFoldD` (kernel-checked
/// totality; motive `λ_. Int → OptE`), prove per-ctor guard-true adequacy +
/// guard-false theorems (∀-quantified over the depth, binder children's IHs
/// at `dsucc d`), and the `memoAdequateD` theorem (oracle keyed on
/// `(node, depth)` — P-ADDR's rung-D residence). `claims` overrides the
/// guard-TRUE RHS per ctor — the FAIL-CLOSED PROBE mechanism (an IH claimed
/// at `d` where the honest minor has `dsucc d`, or vice versa, is not def-eq
/// → `KernelRejected`).
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn check_expr_fold_refinement_claimed_d(
    ctors: &[TCtor],
    claims: &[Option<Expr>],
) -> RefinementVerdict {
    let (mut env, names) = match build_expr_fold_env_d(ctors) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let t_ty = || cst(&names.texpr);
    let mut residue_names: Vec<String> = Vec::new();

    for (i, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let ctor_const = cst(&names.ctors[i]);
        // ctor applied to the field binders at shift s (above d).
        let ctor_app = |s: u32| -> Expr {
            let args: Vec<Expr> = (0..n).map(|f| st_field_d(n, f, s)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let g_app = |s: u32| Expr::apps(st_slot_d(n, 0, s), [ctor_app(s), st_dvar(s)]);

        // Wrap statement/proof in the shared Π/λ telescope: slots + fields +
        // the depth binder.
        let wrap = |mut e: Expr, pi: bool| -> Expr {
            // d innermost of the shared prefix.
            e = if pi { Expr::pi(bd(), int_ty(), e) } else { Expr::lam(bd(), int_ty(), e) };
            for k in ctor.fields.iter().rev() {
                let dom = match k {
                    TField::Rec => t_ty(),
                    TField::Payload => int_ty(),
                };
                e = if pi { Expr::pi(bd(), dom, e) } else { Expr::lam(bd(), dom, e) };
            }
            for si in (0..N_SLOTS_D).rev() {
                let d = slot_ty_d(si, &names);
                e = if pi { Expr::pi(bd(), d, e) } else { Expr::lam(bd(), d, e) };
            }
            e
        };

        for polarity in [true, false] {
            let bool_lit = cst(if polarity { "Bool.true" } else { "Bool.false" });
            // Hypothesis: Eq Bool (G (C xs) d) <polarity>  (s = 0 above d).
            let hyp = Expr::apps(eq_const(), [cst("Bool"), g_app(0), bool_lit.clone()]);
            // RHS under the hypothesis binder (s = 1).
            let honest_rhs = if polarity {
                match statement_rhs_d(&names, ctor, &names.ctors[i], n, 1) {
                    Ok(e) => e,
                    Err(e) => {
                        return RefinementVerdict::KernelRejected(format!(
                            "rhs_d({}): {e}",
                            ctor.name
                        ));
                    }
                }
            } else {
                opte_none(&names)
            };
            let rhs = if polarity {
                claims.get(i).and_then(Option::as_ref).cloned().unwrap_or(honest_rhs)
            } else {
                honest_rhs
            };
            let lhs = st_fold_app_d(&names, n, ctor_app(1), st_dvar(1), 1);
            let eq = Expr::apps(eq_const(), [opte_ty(&names), lhs, rhs]);
            let statement = wrap(Expr::pi(bd(), hyp.clone(), eq), true);

            // Proof: congrArg (λ b. Bool.rec (λ_.OptE) none <honest arm @ s=2> b) h.
            let f_lam = {
                let arm = match statement_rhs_d(&names, ctor, &names.ctors[i], n, 2) {
                    Ok(e) => e,
                    Err(e) => {
                        return RefinementVerdict::KernelRejected(format!(
                            "proof-arm_d({}): {e}",
                            ctor.name
                        ));
                    }
                };
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
                let motive = Expr::lam(bd(), cst("Bool"), opte_ty(&names));
                Expr::lam(
                    bd(),
                    cst("Bool"),
                    Expr::apps(bool_rec, [motive, opte_none(&names), arm, Expr::bvar(0)]),
                )
            };
            let congr = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
                [cst("Bool"), opte_ty(&names), g_app(1), bool_lit, f_lam, Expr::bvar(0)],
            );
            let proof = wrap(Expr::lam(bd(), hyp, congr), false);

            {
                let tc = TypeChecker::new(&env);
                if let Err(e) = tc.check_type(&proof, &statement) {
                    return RefinementVerdict::KernelRejected(format!(
                        "check_type[{} {} depth]: {e:?}",
                        ctor.name,
                        if polarity { "guard-true" } else { "guard-false" }
                    ));
                }
            }
            let decl_name = Name::from_string(&format!(
                "Trust.TrustIr.Refinement.expr_foldd_arm{i}_{}_{}",
                ctor.name,
                if polarity { "gtrue" } else { "gfalse" }
            ));
            if let Err(e) = env.add_decl(Declaration::Theorem {
                name: decl_name.clone(),
                level_params: vec![],
                type_: statement,
                value: proof,
            }) {
                return RefinementVerdict::KernelRejected(format!(
                    "add_decl[{} depth]: {e:?}",
                    ctor.name
                ));
            }
            match env.axiom_deps(&decl_name) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
                None => {
                    return RefinementVerdict::KernelRejected(format!(
                        "decl not found after add: {} (depth)",
                        ctor.name
                    ));
                }
            }
        }
    }

    // memoAdequateD — the depth-keyed conditional memo-adequacy theorem;
    // P-ADDR (over the (node, depth) PAIR) lives in its hypothesis.
    match build_memo_adequate_d(&names, ctors) {
        Ok((statement, proof)) => {
            {
                let tc = TypeChecker::new(&env);
                if let Err(e) = tc.check_type(&proof, &statement) {
                    return RefinementVerdict::KernelRejected(format!(
                        "check_type[memoAdequateD]: {e:?}"
                    ));
                }
            }
            let decl_name = Name::from_string(&format!("{NS}.memoAdequateD"));
            if let Err(e) = env.add_decl(Declaration::Theorem {
                name: decl_name.clone(),
                level_params: vec![],
                type_: statement,
                value: proof,
            }) {
                return RefinementVerdict::KernelRejected(format!(
                    "add_decl[memoAdequateD]: {e:?}"
                ));
            }
            match env.axiom_deps(&decl_name) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
                None => {
                    return RefinementVerdict::KernelRejected(
                        "memoAdequateD not found after add".to_string(),
                    );
                }
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("memoAdequateD: {e}")),
    }

    if residue_names.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue_names.sort();
        residue_names.dedup();
        RefinementVerdict::Residue(residue_names)
    }
}

/// The honest (no-claims) depth-family check.
#[must_use]
pub fn check_expr_fold_refinement_d(ctors: &[TCtor]) -> RefinementVerdict {
    check_expr_fold_refinement_claimed_d(ctors, &[])
}

/// Build `memoAdequate`'s statement + proof (see the module doc).
#[allow(clippy::too_many_lines)]
fn build_memo_adequate(names: &WitnessNames, ctors: &[TCtor]) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    let lk_fn_ty = || Expr::pi(bd(), t_ty(), cst(&names.lk));
    let lzero = Level::zero();

    // Outer telescope: slots(6), lk, snd — accessors at `k` extra binders.
    let slotv = |i: usize, k: u32| Expr::bvar(k + u32::try_from(7 - i).unwrap_or(0));
    let lkv = |k: u32| Expr::bvar(k + 1);
    let sndv = |k: u32| Expr::bvar(k);
    let fold_app = |e: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, k)).collect();
        args.push(e);
        Expr::apps(cst(&names.fold), args)
    };
    let memo_app = |e: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, k)).collect();
        args.push(lkv(k));
        args.push(e);
        Expr::apps(cst(&names.memo_fold), args)
    };

    // snd : Π (e : TExpr) (r : OptE), Eq Lk (lk e) (Lk.hit r) → Eq OptE r (foldE slots e)
    // (declared UNDER slots+lk, so k inside counts binders past those 7).
    let snd_ty = {
        // under e: k=1 relative to (slots+lk) → but our accessors assume the
        // full 8-binder telescope; snd's type is formed after 7 binders
        // (slots + lk), so slot i = bvar((7-1) - i + extra)… Build with local
        // offsets: under Π e (1 extra past 7) and Π r (2) and hyp (—):
        let slotv7 = |i: usize, extra: u32| Expr::bvar(extra + u32::try_from(6 - i).unwrap_or(0));
        let lkv7 = |extra: u32| Expr::bvar(extra);
        let hyp = Expr::apps(
            eq_const(),
            [
                cst(&names.lk),
                Expr::app(lkv7(2), Expr::bvar(1)),
                Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
            ],
        );
        let concl = {
            let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv7(i, 3)).collect();
            args.push(Expr::bvar(2)); // e
            Expr::apps(
                eq_const(),
                [
                    opte_ty(names),
                    Expr::bvar(1), // r  (under hyp binder: r = bvar 1)
                    Expr::apps(cst(&names.fold), args),
                ],
            )
        };
        Expr::pi(bd(), t_ty(), Expr::pi(bd(), opte_ty(names), Expr::pi(bd(), hyp, concl)))
    };

    // Statement: Π slots Π lk Π snd Π e, Eq OptE (memoFoldE … e) (foldE … e).
    let statement = {
        let concl = Expr::apps(
            eq_const(),
            [opte_ty(names), memo_app(Expr::bvar(0), 1), fold_app(Expr::bvar(0), 1)],
        );
        let mut st = Expr::pi(bd(), t_ty(), concl);
        st = Expr::pi(bd(), snd_ty.clone(), st);
        st = Expr::pi(bd(), lk_fn_ty(), st);
        for i in (0..N_SLOTS).rev() {
            st = Expr::pi(bd(), slot_ty(i, names), st);
        }
        st
    };

    // Proof: λ slots λ lk λ snd. TExpr.rec.{0} motive minors…
    let texpr_rec_p = Expr::const_(Name::from_string(&format!("{}.rec", names.texpr)), vec![lzero]);
    let motive = Expr::lam(
        bd(),
        t_ty(),
        Expr::apps(
            eq_const(),
            [opte_ty(names), memo_app(Expr::bvar(0), 1), fold_app(Expr::bvar(0), 1)],
        ),
    );
    let mut rec_args: Vec<Expr> = vec![motive];

    for (ci, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let rec_positions: Vec<usize> = ctor
            .fields
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == TField::Rec)
            .map(|(i, _)| i)
            .collect();
        let m = rec_positions.len();
        let nm = u32::try_from(n + m).map_err(|_| "binder overflow".to_string())?;
        // Inside the pminor telescope (fields + ih-proofs) + s extra binders,
        // the OUTER accessors take k = nm + s.
        let fieldv = {
            move |f: usize, s: u32| Expr::bvar(u32::try_from(n + m - 1 - f).unwrap_or(u32::MAX) + s)
        };
        let ihpv = {
            let rp = rec_positions.clone();
            move |f: usize, s: u32| {
                let j = rp.iter().position(|p| *p == f).unwrap_or(usize::MAX);
                Expr::bvar(u32::try_from(m - 1 - j).unwrap_or(u32::MAX) + s)
            }
        };
        let ctor_const = cst(&names.ctors[ci]);
        let ctor_app = |s: u32| -> Expr {
            let args: Vec<Expr> = (0..n).map(|f| fieldv(f, s)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let scrut = |s: u32| Expr::app(lkv(nm + s), ctor_app(s));
        let g_app = |s: u32| Expr::app(slotv(0, nm + s), ctor_app(s));

        // armE with a CHOICE of IH rendering per rec position:
        //   `folded_below` positions < t render as foldE-applications;
        //   position == `hole` renders as the congr-lambda's bound var;
        //   the rest render as memoFoldE-applications.
        // `s0` = extra binders at the ARM TOP (the hole var was bound at
        // s0 − 1 … i.e. the hole is bvar(s'' − s0) at internal shift s'').
        let arm_mixed = |t: usize, hole: Option<usize>, s0: u32| -> Result<Expr, String> {
            let ih = {
                let rp = rec_positions.clone();
                move |f: usize, s2: u32| {
                    let p = rp.iter().position(|q| *q == f).unwrap_or(usize::MAX);
                    if p < t {
                        fold_app(fieldv(f, s2), nm + s2)
                    } else if Some(p) == hole {
                        Expr::bvar(s2 - s0)
                    } else {
                        memo_app(fieldv(f, s2), nm + s2)
                    }
                }
            };
            let slot = move |i: usize, s2: u32| slotv(i, nm + s2);
            let field = move |f: usize, s2: u32| fieldv(f, s2);
            arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, None, s0)
        };
        // The guarded value with mixed IHs at shift s.
        let guarded_mixed = |t: usize, hole: Option<usize>, s0: u32| -> Result<Expr, String> {
            let arm = arm_mixed(t, hole, s0)?;
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
            let bmotive = Expr::lam(bd(), cst("Bool"), opte_ty(names));
            Ok(Expr::apps(bool_rec, [bmotive, opte_none(names), arm, g_app(s0)]))
        };

        // The dependent Lk.rec case split.
        let lk_rec0 =
            Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![Level::zero()]);
        let lk_rec1 = Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![l1()]);
        // matchTerm(o, s) — the memoFoldE reduct's match with scrutinee o.
        let match_term = |o: Expr, s: u32| -> Result<Expr, String> {
            let miss = guarded_mixed(0, None, s)?;
            let hit = Expr::lam(bd(), opte_ty(names), Expr::bvar(0));
            let lmotive = Expr::lam(bd(), cst(&names.lk), opte_ty(names));
            Ok(Expr::apps(lk_rec1.clone(), [lmotive, miss, hit, o]))
        };

        // Dependent motive: λ o. Π (h : Eq Lk scrut o), Eq OptE (match o) (foldE (C xs)).
        let dep_motive = {
            let hyp = Expr::apps(eq_const(), [cst(&names.lk), scrut(1), Expr::bvar(0)]);
            let concl = Expr::apps(
                eq_const(),
                [opte_ty(names), match_term(Expr::bvar(1), 2)?, fold_app(ctor_app(2), nm + 2)],
            );
            Expr::lam(bd(), cst(&names.lk), Expr::pi(bd(), hyp, concl))
        };

        // case_miss: λ h. <IH chain>  (s = 1 under h).
        let case_miss = {
            let s = 1u32;
            let chain: Expr = if m == 0 {
                eq_refl(opte_ty(names), fold_app(ctor_app(s), nm + s))
            } else {
                // step_j at shift s.
                let step = |j: usize| -> Result<Expr, String> {
                    let f_lam = {
                        // λ y : OptE. guarded value with hole at position j
                        // (arm top shift s+1; the hole bound at s+1).
                        let body = guarded_mixed(j, Some(j), s + 1)?;
                        Expr::lam(bd(), opte_ty(names), body)
                    };
                    let fj = rec_positions[j];
                    Ok(Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
                        [
                            opte_ty(names),
                            opte_ty(names),
                            memo_app(fieldv(fj, s), nm + s),
                            fold_app(fieldv(fj, s), nm + s),
                            f_lam,
                            ihpv(fj, s),
                        ],
                    ))
                };
                let val_at = |t: usize| guarded_mixed(t, None, s);
                let mut acc = step(0)?;
                for j in 1..m {
                    acc = Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![l1()]),
                        [opte_ty(names), val_at(0)?, val_at(j)?, val_at(j + 1)?, acc, step(j)?],
                    );
                }
                acc
            };
            let hyp = Expr::apps(
                eq_const(),
                [cst(&names.lk), scrut(0), cst(&format!("{}.miss", names.lk))],
            );
            Expr::lam(bd(), hyp, chain)
        };

        // case_hit: λ r λ h. snd (C xs) r h.
        let case_hit = {
            let hyp = Expr::apps(
                eq_const(),
                [
                    cst(&names.lk),
                    scrut(1),
                    Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
                ],
            );
            let body = Expr::apps(sndv(nm + 2), [ctor_app(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), opte_ty(names), Expr::lam(bd(), hyp, body))
        };

        let split = Expr::apps(lk_rec0, [dep_motive, case_miss, case_hit, scrut(0)]);
        let refl = eq_refl(cst(&names.lk), scrut(0));
        let pbody = Expr::app(split, refl);

        // Wrap the pminor telescope: fields then IH proofs (motive-applied).
        let mut pminor = pbody;
        for j in (0..m).rev() {
            let fj = rec_positions[j];
            // ihp_j : Eq OptE (memoFoldE … x_fj) (foldE … x_fj), with x_fj at
            // the CURRENT binder depth: fields all bound; j IH binders below
            // this one already… under this binder there are (m-1-j) more —
            // the type is formed OUTSIDE its own binder: extra = j IH binders
            // so far → s = j as seen from the fields… Compute: at the point
            // of the j-th IH binder (outermost IH first), binders so far =
            // n + j, so x_f = bvar(n + j - 1 - f) and outer k = n + j.
            let x = Expr::bvar(u32::try_from(n + j - 1 - fj).unwrap_or(u32::MAX));
            let k = u32::try_from(n + j).map_err(|_| "k overflow".to_string())?;
            let ty =
                Expr::apps(eq_const(), [opte_ty(names), memo_app(x.clone(), k), fold_app(x, k)]);
            pminor = Expr::lam(bd(), ty, pminor);
        }
        for kf in ctor.fields.iter().rev() {
            let dom = match kf {
                TField::Rec => t_ty(),
                TField::Payload => int_ty(),
            };
            pminor = Expr::lam(bd(), dom, pminor);
        }
        rec_args.push(pminor);
    }

    let mut proof = Expr::apps(texpr_rec_p, rec_args);
    proof = Expr::lam(bd(), snd_ty, proof);
    proof = Expr::lam(bd(), lk_fn_ty(), proof);
    for i in (0..N_SLOTS).rev() {
        proof = Expr::lam(bd(), slot_ty(i, names), proof);
    }
    Ok((statement, proof))
}

/// RUNG D — build `memoAdequateD`'s statement + proof: the depth-keyed
/// generalization of [`build_memo_adequate`]. The lookup oracle is
/// `lk : TExpr → Int → Lk` and the oracle-soundness hypothesis quantifies
/// over BOTH the node and the depth:
///
/// ```text
/// memoAdequateD : ∀ slots(7) (lk)
///   (snd : Π (e : TExpr) (d : Int) (r : OptE),
///          Eq Lk (lk e d) (Lk.hit r) → Eq OptE r (foldD slots e d)),
///   Π (e : TExpr) (d : Int), Eq OptE (memoFoldD slots lk e d) (foldD slots e d)
/// ```
///
/// proven by `TExpr.rec` at a Π-over-depth motive — each minor's miss branch
/// rewrites the memo child applications to fold applications via the IH
/// APPLIED AT THE CHILD'S DEPTH (`ihp_j d` / `ihp_j (dsucc d)` per the binder
/// marks); the hit branch is the oracle hypothesis at `(C xs, d)`.
#[allow(clippy::too_many_lines)]
fn build_memo_adequate_d(names: &WitnessNames, ctors: &[TCtor]) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    let lk_fn_ty = || Expr::pi(bd(), t_ty(), Expr::pi(bd(), int_ty(), cst(&names.lk)));
    let lzero = Level::zero();

    // Outer telescope: slots(7), lk, snd — accessors at `k` extra binders.
    let slotv = |i: usize, k: u32| Expr::bvar(k + u32::try_from(8 - i).unwrap_or(0));
    let lkv = |k: u32| Expr::bvar(k + 1);
    let sndv = |k: u32| Expr::bvar(k);
    let fold_app = |e: Expr, dd: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv(i, k)).collect();
        args.push(e);
        args.push(dd);
        Expr::apps(cst(&names.fold), args)
    };
    let memo_app = |e: Expr, dd: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv(i, k)).collect();
        args.push(lkv(k));
        args.push(e);
        args.push(dd);
        Expr::apps(cst(&names.memo_fold), args)
    };

    // snd : Π (e : TExpr) (d : Int) (r : OptE),
    //       Eq Lk (lk e d) (Lk.hit r) → Eq OptE r (foldD slots e d)
    // (declared UNDER slots+lk; local accessors relative to those 8 binders).
    let snd_ty = {
        let slotv8 =
            |i: usize, extra: u32| Expr::bvar(extra + 1 + u32::try_from(6 - i).unwrap_or(0));
        let lkv8 = |extra: u32| Expr::bvar(extra);
        // Under e (bvar 2 at extra=3), d (bvar 1), r (bvar 0):
        let hyp = Expr::apps(
            eq_const(),
            [
                cst(&names.lk),
                Expr::apps(lkv8(3), [Expr::bvar(2), Expr::bvar(1)]),
                Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
            ],
        );
        let concl = {
            let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv8(i, 4)).collect();
            args.push(Expr::bvar(3)); // e
            args.push(Expr::bvar(2)); // d
            Expr::apps(
                eq_const(),
                [
                    opte_ty(names),
                    Expr::bvar(1), // r (under the hyp binder)
                    Expr::apps(cst(&names.fold), args),
                ],
            )
        };
        Expr::pi(
            bd(),
            t_ty(),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), opte_ty(names), Expr::pi(bd(), hyp, concl))),
        )
    };

    // Statement: Π slots lk snd (e) (d), Eq OptE (memoFoldD … e d) (foldD … e d).
    let statement = {
        let concl = Expr::apps(
            eq_const(),
            [
                opte_ty(names),
                memo_app(Expr::bvar(1), Expr::bvar(0), 2),
                fold_app(Expr::bvar(1), Expr::bvar(0), 2),
            ],
        );
        let mut st = Expr::pi(bd(), int_ty(), concl);
        st = Expr::pi(bd(), t_ty(), st);
        st = Expr::pi(bd(), snd_ty.clone(), st);
        st = Expr::pi(bd(), lk_fn_ty(), st);
        for i in (0..N_SLOTS_D).rev() {
            st = Expr::pi(bd(), slot_ty_d(i, names), st);
        }
        st
    };

    // Proof: λ slots λ lk λ snd. TExpr.rec.{0} motive minors…
    let texpr_rec_p = Expr::const_(Name::from_string(&format!("{}.rec", names.texpr)), vec![lzero]);
    let motive = Expr::lam(
        bd(),
        t_ty(),
        Expr::pi(
            bd(),
            int_ty(),
            Expr::apps(
                eq_const(),
                [
                    opte_ty(names),
                    memo_app(Expr::bvar(1), Expr::bvar(0), 2),
                    fold_app(Expr::bvar(1), Expr::bvar(0), 2),
                ],
            ),
        ),
    );
    let mut rec_args: Vec<Expr> = vec![motive];

    for (ci, ctor) in ctors.iter().enumerate() {
        let n = ctor.fields.len();
        let rec_positions: Vec<usize> = ctor
            .fields
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == TField::Rec)
            .map(|(i, _)| i)
            .collect();
        let m = rec_positions.len();
        let nm = u32::try_from(n + m).map_err(|_| "binder overflow".to_string())?;
        // Inside the pminor telescope (fields + ih-proofs + the λd binder) +
        // `s` extra binders above d, the OUTER accessors take k = nm + 1 + s.
        let kk = move |s: u32| nm + 1 + s;
        let fieldv = {
            move |f: usize, s: u32| {
                Expr::bvar(u32::try_from(n + m - 1 - f).unwrap_or(u32::MAX) + 1 + s)
            }
        };
        let ihpv = {
            let rp = rec_positions.clone();
            move |f: usize, s: u32| {
                let j = rp.iter().position(|p| *p == f).unwrap_or(usize::MAX);
                Expr::bvar(u32::try_from(m - 1 - j).unwrap_or(u32::MAX) + 1 + s)
            }
        };
        let dvar = |s: u32| Expr::bvar(s);
        let ddep = {
            move |f: usize, s: u32| {
                if ctor_child_is_binder(ctor, f) {
                    Expr::app(slotv(1, kk(s)), dvar(s))
                } else {
                    dvar(s)
                }
            }
        };
        let ctor_const = cst(&names.ctors[ci]);
        let ctor_app = |s: u32| -> Expr {
            let args: Vec<Expr> = (0..n).map(|f| fieldv(f, s)).collect();
            Expr::apps(ctor_const.clone(), args)
        };
        let scrut = |s: u32| Expr::apps(lkv(kk(s)), [ctor_app(s), dvar(s)]);
        let g_app = |s: u32| Expr::apps(slotv(0, kk(s)), [ctor_app(s), dvar(s)]);

        // armD with a CHOICE of IH rendering per rec position (see the
        // depthless `arm_mixed`); every IH application is at the CHILD's
        // depth (`d` / `dsucc d`).
        let arm_mixed = |t: usize, hole: Option<usize>, s0: u32| -> Result<Expr, String> {
            let ih = {
                let rp = rec_positions.clone();
                move |f: usize, s2: u32| {
                    let p = rp.iter().position(|q| *q == f).unwrap_or(usize::MAX);
                    if p < t {
                        fold_app(fieldv(f, s2), ddep(f, s2), kk(s2))
                    } else if Some(p) == hole {
                        Expr::bvar(s2 - s0)
                    } else {
                        memo_app(fieldv(f, s2), ddep(f, s2), kk(s2))
                    }
                }
            };
            let slot = move |i: usize, s2: u32| slotv(i, kk(s2));
            let field = move |f: usize, s2: u32| fieldv(f, s2);
            let dexp = move |s2: u32| dvar(s2);
            arm_expr(names, ctor, &ctor_const, &slot, &field, &ih, Some(&dexp), s0)
        };
        let guarded_mixed = |t: usize, hole: Option<usize>, s0: u32| -> Result<Expr, String> {
            let arm = arm_mixed(t, hole, s0)?;
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
            let bmotive = Expr::lam(bd(), cst("Bool"), opte_ty(names));
            Ok(Expr::apps(bool_rec, [bmotive, opte_none(names), arm, g_app(s0)]))
        };

        // The dependent Lk.rec case split.
        let lk_rec0 =
            Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![Level::zero()]);
        let lk_rec1 = Expr::const_(Name::from_string(&format!("{}.rec", names.lk)), vec![l1()]);
        let match_term = |o: Expr, s: u32| -> Result<Expr, String> {
            let miss = guarded_mixed(0, None, s)?;
            let hit = Expr::lam(bd(), opte_ty(names), Expr::bvar(0));
            let lmotive = Expr::lam(bd(), cst(&names.lk), opte_ty(names));
            Ok(Expr::apps(lk_rec1.clone(), [lmotive, miss, hit, o]))
        };

        // Dependent motive: λ o. Π (h : Eq Lk scrut o),
        //   Eq OptE (match o) (foldD (C xs) d).
        let dep_motive = {
            let hyp = Expr::apps(eq_const(), [cst(&names.lk), scrut(1), Expr::bvar(0)]);
            let concl = Expr::apps(
                eq_const(),
                [
                    opte_ty(names),
                    match_term(Expr::bvar(1), 2)?,
                    fold_app(ctor_app(2), dvar(2), kk(2)),
                ],
            );
            Expr::lam(bd(), cst(&names.lk), Expr::pi(bd(), hyp, concl))
        };

        // case_miss: λ h. <IH chain>  (s = 1 under h).
        let case_miss = {
            let s = 1u32;
            let chain: Expr = if m == 0 {
                eq_refl(opte_ty(names), fold_app(ctor_app(s), dvar(s), kk(s)))
            } else {
                let step = |j: usize| -> Result<Expr, String> {
                    let f_lam = {
                        let body = guarded_mixed(j, Some(j), s + 1)?;
                        Expr::lam(bd(), opte_ty(names), body)
                    };
                    let fj = rec_positions[j];
                    Ok(Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
                        [
                            opte_ty(names),
                            opte_ty(names),
                            memo_app(fieldv(fj, s), ddep(fj, s), kk(s)),
                            fold_app(fieldv(fj, s), ddep(fj, s), kk(s)),
                            f_lam,
                            Expr::app(ihpv(fj, s), ddep(fj, s)),
                        ],
                    ))
                };
                let val_at = |t: usize| guarded_mixed(t, None, s);
                let mut acc = step(0)?;
                for j in 1..m {
                    acc = Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![l1()]),
                        [opte_ty(names), val_at(0)?, val_at(j)?, val_at(j + 1)?, acc, step(j)?],
                    );
                }
                acc
            };
            let hyp = Expr::apps(
                eq_const(),
                [cst(&names.lk), scrut(0), cst(&format!("{}.miss", names.lk))],
            );
            Expr::lam(bd(), hyp, chain)
        };

        // case_hit: λ r λ h. snd (C xs) d r h.
        let case_hit = {
            let hyp = Expr::apps(
                eq_const(),
                [
                    cst(&names.lk),
                    scrut(1),
                    Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
                ],
            );
            let body =
                Expr::apps(sndv(kk(2)), [ctor_app(2), dvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), opte_ty(names), Expr::lam(bd(), hyp, body))
        };

        let split = Expr::apps(lk_rec0, [dep_motive, case_miss, case_hit, scrut(0)]);
        let refl = eq_refl(cst(&names.lk), scrut(0));
        let pbody = Expr::app(split, refl);

        // Wrap: λ fields λ ihps λ (d : Int). pbody — IH proofs are
        // Π-over-depth (the motive applied to the child).
        let mut pminor = Expr::lam(bd(), int_ty(), pbody);
        for j in (0..m).rev() {
            let fj = rec_positions[j];
            // At the j-th IH binder: binders so far = n + j; its type binds
            // its own d' (so x_fj shifts by 1 and the outer k = n + j + 1).
            let x = Expr::bvar(u32::try_from(n + j - 1 - fj).unwrap_or(u32::MAX) + 1);
            let k = u32::try_from(n + j + 1).map_err(|_| "k overflow".to_string())?;
            let ty = Expr::pi(
                bd(),
                int_ty(),
                Expr::apps(
                    eq_const(),
                    [
                        opte_ty(names),
                        memo_app(x.clone(), Expr::bvar(0), k),
                        fold_app(x, Expr::bvar(0), k),
                    ],
                ),
            );
            pminor = Expr::lam(bd(), ty, pminor);
        }
        for kf in ctor.fields.iter().rev() {
            let dom = match kf {
                TField::Rec => t_ty(),
                TField::Payload => int_ty(),
            };
            pminor = Expr::lam(bd(), dom, pminor);
        }
        rec_args.push(pminor);
    }

    let mut proof = Expr::apps(texpr_rec_p, rec_args);
    proof = Expr::lam(bd(), snd_ty, proof);
    proof = Expr::lam(bd(), lk_fn_ty(), proof);
    for i in (0..N_SLOTS_D).rev() {
        proof = Expr::lam(bd(), slot_ty_d(i, names), proof);
    }
    Ok((statement, proof))
}

// ===========================================================================
// The cached universal-witness verdict (design §7's env-budget item)
// ===========================================================================

/// The universal witness is FOLDER-INDEPENDENT (leaf-parametric), so one
/// kernel-checked build serves every row recognized against the same ctor
/// table. Cache the verdict keyed by the table's structural fingerprint —
/// deterministic, input-pinned, sound to reuse. The measured build cost and
/// cache behavior are part of the rung-C report (design §7).
static WITNESS_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<String, (RefinementVerdict, std::time::Duration)>>,
> = std::sync::OnceLock::new();

/// Cached honest check; returns the verdict and the (first-build) wall cost.
#[must_use]
pub fn check_expr_fold_refinement_cached(
    ctors: &[TCtor],
) -> (RefinementVerdict, std::time::Duration) {
    let key = format!("{ctors:?}");
    let cache =
        WITNESS_CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((v, d)) = guard.get(&key) {
            return (v.clone(), *d);
        }
    }
    let t0 = std::time::Instant::now();
    let verdict = check_expr_fold_refinement(ctors);
    let dt = t0.elapsed();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, (verdict.clone(), dt));
    }
    (verdict, dt)
}

/// Rung D: the cached honest DEPTH-FAMILY check (`foldD`/`memoFoldD` +
/// memoAdequateD). Same cache, key namespaced — the depth witness is also
/// folder-independent (leaf-/dsucc-parametric), so the five depth folders
/// share one kernel build.
#[must_use]
pub fn check_expr_fold_refinement_cached_d(
    ctors: &[TCtor],
) -> (RefinementVerdict, std::time::Duration) {
    let key = format!("D:{ctors:?}");
    let cache =
        WITNESS_CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((v, d)) = guard.get(&key) {
            return (v.clone(), *d);
        }
    }
    let t0 = std::time::Instant::now();
    let verdict = check_expr_fold_refinement_d(ctors);
    let dt = t0.elapsed();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, (verdict.clone(), dt));
    }
    (verdict, dt)
}

// ===========================================================================
// RUNG E — the G-family wrapper witnesses (design §3.4 + §5 Rung E)
//
// Two kernel pieces, both consuming the SAME registered fold denotation the
// rung-C/D SCC certificates established (the `foldE`/`foldD` model term over
// the recognized 33-ctor table):
//
//   1. THE LAUNCH COMPOSITION THEOREM (`wrapAdequate` / `wrapAdequateD`) —
//      the kernel-checked model of `fold_opt_or_clone`'s
//      `fold_expr_opt(..).unwrap_or_else(|| self.clone())` composition:
//
//        wrapAdequate : ∀ slots lk snd e,
//          unwrapOr (memoFoldE slots lk e) e = unwrapOr (foldE slots e) e
//
//      (`unwrapOr o e` = `OptE.rec (λ_.TExpr) e (λ x. x) o`, inlined), proven
//      by `congrArg` over the REGISTERED `memoAdequate` theorem — so the
//      wrapper's certificate consumes the callee's certified fold denotation
//      THROUGH the same oracle-soundness hypothesis (P-ADDR residence
//      unchanged; `axiom_deps` empty). The `_d` twin composes `memoAdequateD`
//      at `∀ e d`. The `claims` hook mirrors the per-ctor probe mechanism: a
//      claimed conclusion RHS not def-eq to the honest unwrap composition is
//      `KernelRejected` (probes: the identity claim `= e`, the
//      swapped-eliminator claim `some ↦ e`).
//
//   2. THE ADT-VALUED CALL TRANSPORT (`CallE`/`callResultE` — design §3.4
//      option (a), the TExpr-sorted twin of `trustir_call.rs`'s Int
//      machinery): `CallE.mk : Nat → Operand → TExpr → CallE`,
//      `callResultE : CallE → TExpr` (recursor projection),
//      and a per-call-site `callReturnInstanceE` pinned at the concrete
//      `CallE.mk <id> <arg>` whose hypothesis is `post ret` and conclusion is
//      `post (callResultE (CallE.mk id arg ret))`. This is the composition
//      artifact: the kernel must reduce the concrete projection to the exact
//      separately-certified callee return, rather than checking the former
//      zero-content `P(callResultE c) → P(callResultE c)` identity.
//      Registered over the SAME `TExpr` mirror as the fold witness, so the
//      transported value lives in the fold lane's own value domain — the
//      "denotation-carrying" widening: an ADT-valued callee return is no
//      longer forced onto the Int carrier. Same fail-closed hook
//      (`claimed_concl_pred`): a wrong postcondition is `KernelRejected`.
// ===========================================================================

/// `unwrapOr o e` — the inlined `OptE.rec.{1} (λ_. TExpr) e (λ x. x) o`
/// eliminator (the model of `Option::unwrap_or_else(.., || self.clone())`
/// under P-CLONE + P-OPT-STD).
fn unwrap_or_e(names: &WitnessNames, o: Expr, e: Expr) -> Expr {
    let rec = Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
    let motive = Expr::lam(bd(), opte_ty(names), texpr_ty(names));
    let some_arm = Expr::lam(bd(), texpr_ty(names), Expr::bvar(0));
    Expr::apps(rec, [motive, e, some_arm, o])
}

/// The rung-E probe RHS: the SWAPPED-ELIMINATOR forgery (`some ↦ e` — the
/// wrapper claimed to discard the fold result). Rendered under the
/// depthless `wrapAdequate` conclusion binders (slots, lk, snd, e); MUST be
/// `KernelRejected` by [`check_expr_fold_wrap_refinement_claimed`].
#[must_use]
pub fn probe_wrap_rhs_swapped(ctors: &[TCtor]) -> Expr {
    let names = witness_names(ctors);
    let rec = Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
    let motive = Expr::lam(bd(), opte_ty(&names), texpr_ty(&names));
    // some ↦ e (payload DISCARDED; e is bvar 0 outside, bvar 1 under the λ).
    let some_arm = Expr::lam(bd(), texpr_ty(&names), Expr::bvar(1));
    let fold_app = {
        let slotv = |i: usize, k: u32| Expr::bvar(k + u32::try_from(7 - i).unwrap_or(0));
        let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, 1)).collect();
        args.push(Expr::bvar(0));
        Expr::apps(cst(&names.fold), args)
    };
    Expr::apps(rec, [motive, Expr::bvar(0), some_arm, fold_app])
}

/// Build the `wrapAdequate` statement + proof (depthless). The env must
/// already hold `{NS}.memoAdequate` (registered by the caller from
/// [`build_memo_adequate`]). `claim` overrides the conclusion RHS (probe
/// hook). Statement:
///
///   Π slots(6) Π lk Π snd Π e,
///     Eq TExpr (unwrapOr (memoFoldE slots lk e) e)
///              (unwrapOr (foldE slots e) e)
///
/// Proof: `λ slots lk snd e. congrArg (λ o. unwrapOr o e)
/// (memoAdequate slots lk snd e)`.
fn build_wrap_adequate(names: &WitnessNames, claim: Option<&Expr>) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    let lk_fn_ty = || Expr::pi(bd(), t_ty(), cst(&names.lk));
    // Outer telescope accessors (identical to build_memo_adequate's).
    let slotv = |i: usize, k: u32| Expr::bvar(k + u32::try_from(7 - i).unwrap_or(0));
    let lkv = |k: u32| Expr::bvar(k + 1);
    let sndv = |k: u32| Expr::bvar(k);
    let fold_app = |e: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, k)).collect();
        args.push(e);
        Expr::apps(cst(&names.fold), args)
    };
    let memo_app = |e: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, k)).collect();
        args.push(lkv(k));
        args.push(e);
        Expr::apps(cst(&names.memo_fold), args)
    };
    // snd : Π (e : TExpr) (r : OptE), Eq Lk (lk e) (Lk.hit r) → Eq OptE r (foldE slots e)
    // — BYTE-IDENTICAL to build_memo_adequate's hypothesis type.
    let snd_ty = {
        let slotv7 = |i: usize, extra: u32| Expr::bvar(extra + u32::try_from(6 - i).unwrap_or(0));
        let lkv7 = |extra: u32| Expr::bvar(extra);
        let hyp = Expr::apps(
            eq_const(),
            [
                cst(&names.lk),
                Expr::app(lkv7(2), Expr::bvar(1)),
                Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
            ],
        );
        let concl = {
            let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv7(i, 3)).collect();
            args.push(Expr::bvar(2));
            Expr::apps(
                eq_const(),
                [opte_ty(names), Expr::bvar(1), Expr::apps(cst(&names.fold), args)],
            )
        };
        Expr::pi(bd(), t_ty(), Expr::pi(bd(), opte_ty(names), Expr::pi(bd(), hyp, concl)))
    };

    // Statement.
    let honest_rhs = unwrap_or_e(names, fold_app(Expr::bvar(0), 1), Expr::bvar(0));
    let rhs = claim.cloned().unwrap_or(honest_rhs);
    let lhs = unwrap_or_e(names, memo_app(Expr::bvar(0), 1), Expr::bvar(0));
    let statement = {
        let concl = Expr::apps(eq_const(), [texpr_ty(names), lhs, rhs]);
        let mut st = Expr::pi(bd(), t_ty(), concl);
        st = Expr::pi(bd(), snd_ty.clone(), st);
        st = Expr::pi(bd(), lk_fn_ty(), st);
        for i in (0..N_SLOTS).rev() {
            st = Expr::pi(bd(), slot_ty(i, names), st);
        }
        st
    };

    // Proof: congrArg over the registered memoAdequate.
    let proof = {
        // Under slots+lk+snd+e (k = 1 for slot accessors at the `e` level).
        let f_lam = Expr::lam(
            bd(),
            opte_ty(names),
            // Under the λ o binder everything shifts by 1; e is bvar 1.
            {
                let rec =
                    Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
                let motive = Expr::lam(bd(), opte_ty(names), texpr_ty(names));
                let some_arm = Expr::lam(bd(), texpr_ty(names), Expr::bvar(0));
                Expr::apps(rec, [motive, Expr::bvar(1), some_arm, Expr::bvar(0)])
            },
        );
        let memo_adequate_app = {
            let mut args: Vec<Expr> = (0..N_SLOTS).map(|i| slotv(i, 1)).collect();
            args.push(lkv(1));
            args.push(sndv(1));
            args.push(Expr::bvar(0));
            Expr::apps(cst(&format!("{NS}.memoAdequate")), args)
        };
        let congr = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
            [
                opte_ty(names),
                texpr_ty(names),
                memo_app(Expr::bvar(0), 1),
                fold_app(Expr::bvar(0), 1),
                f_lam,
                memo_adequate_app,
            ],
        );
        let mut pf = Expr::lam(bd(), t_ty(), congr);
        pf = Expr::lam(bd(), snd_ty, pf);
        pf = Expr::lam(bd(), lk_fn_ty(), pf);
        for i in (0..N_SLOTS).rev() {
            pf = Expr::lam(bd(), slot_ty(i, names), pf);
        }
        pf
    };
    Ok((statement, proof))
}

/// The rung-D twin of [`build_wrap_adequate`]: composes `memoAdequateD` at
/// `∀ e d` (env must already hold `{NS}.memoAdequateD`).
fn build_wrap_adequate_d(
    names: &WitnessNames,
    claim: Option<&Expr>,
) -> Result<(Expr, Expr), String> {
    let t_ty = || cst(&names.texpr);
    let lk_fn_ty = || Expr::pi(bd(), t_ty(), Expr::pi(bd(), int_ty(), cst(&names.lk)));
    let slotv = |i: usize, k: u32| Expr::bvar(k + u32::try_from(8 - i).unwrap_or(0));
    let lkv = |k: u32| Expr::bvar(k + 1);
    let sndv = |k: u32| Expr::bvar(k);
    let fold_app = |e: Expr, dd: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv(i, k)).collect();
        args.push(e);
        args.push(dd);
        Expr::apps(cst(&names.fold), args)
    };
    let memo_app = |e: Expr, dd: Expr, k: u32| {
        let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv(i, k)).collect();
        args.push(lkv(k));
        args.push(e);
        args.push(dd);
        Expr::apps(cst(&names.memo_fold), args)
    };
    // snd — BYTE-IDENTICAL to build_memo_adequate_d's hypothesis type.
    let snd_ty = {
        let slotv8 =
            |i: usize, extra: u32| Expr::bvar(extra + 1 + u32::try_from(6 - i).unwrap_or(0));
        let lkv8 = |extra: u32| Expr::bvar(extra);
        let hyp = Expr::apps(
            eq_const(),
            [
                cst(&names.lk),
                Expr::apps(lkv8(3), [Expr::bvar(2), Expr::bvar(1)]),
                Expr::app(cst(&format!("{}.hit", names.lk)), Expr::bvar(0)),
            ],
        );
        let concl = {
            let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv8(i, 4)).collect();
            args.push(Expr::bvar(3));
            args.push(Expr::bvar(2));
            Expr::apps(
                eq_const(),
                [opte_ty(names), Expr::bvar(1), Expr::apps(cst(&names.fold), args)],
            )
        };
        Expr::pi(
            bd(),
            t_ty(),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), opte_ty(names), Expr::pi(bd(), hyp, concl))),
        )
    };

    // Statement: Π slots lk snd (e)(d), Eq TExpr (unwrapOr (memoFoldD … e d) e)
    //                                             (unwrapOr (foldD … e d) e).
    let honest_rhs = unwrap_or_e(names, fold_app(Expr::bvar(1), Expr::bvar(0), 2), Expr::bvar(1));
    let rhs = claim.cloned().unwrap_or(honest_rhs);
    let lhs = unwrap_or_e(names, memo_app(Expr::bvar(1), Expr::bvar(0), 2), Expr::bvar(1));
    let statement = {
        let concl = Expr::apps(eq_const(), [texpr_ty(names), lhs, rhs]);
        let mut st = Expr::pi(bd(), int_ty(), concl);
        st = Expr::pi(bd(), t_ty(), st);
        st = Expr::pi(bd(), snd_ty.clone(), st);
        st = Expr::pi(bd(), lk_fn_ty(), st);
        for i in (0..N_SLOTS_D).rev() {
            st = Expr::pi(bd(), slot_ty_d(i, names), st);
        }
        st
    };

    let proof = {
        let f_lam = Expr::lam(bd(), opte_ty(names), {
            let rec = Expr::const_(Name::from_string(&format!("{}.rec", names.opte)), vec![l1()]);
            let motive = Expr::lam(bd(), opte_ty(names), texpr_ty(names));
            let some_arm = Expr::lam(bd(), texpr_ty(names), Expr::bvar(0));
            // e is bvar 1 at k=2; under λ o it is bvar 2.
            Expr::apps(rec, [motive, Expr::bvar(2), some_arm, Expr::bvar(0)])
        });
        let memo_adequate_app = {
            let mut args: Vec<Expr> = (0..N_SLOTS_D).map(|i| slotv(i, 2)).collect();
            args.push(lkv(2));
            args.push(sndv(2));
            args.push(Expr::bvar(1));
            args.push(Expr::bvar(0));
            Expr::apps(cst(&format!("{NS}.memoAdequateD")), args)
        };
        let congr = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
            [
                opte_ty(names),
                texpr_ty(names),
                memo_app(Expr::bvar(1), Expr::bvar(0), 2),
                fold_app(Expr::bvar(1), Expr::bvar(0), 2),
                f_lam,
                memo_adequate_app,
            ],
        );
        let mut pf = Expr::lam(bd(), int_ty(), congr);
        pf = Expr::lam(bd(), t_ty(), pf);
        pf = Expr::lam(bd(), snd_ty, pf);
        pf = Expr::lam(bd(), lk_fn_ty(), pf);
        for i in (0..N_SLOTS_D).rev() {
            pf = Expr::lam(bd(), slot_ty_d(i, names), pf);
        }
        pf
    };
    Ok((statement, proof))
}

/// Register a checked theorem into `env` and audit its axiom residue into
/// `residues` (the rung-C registration discipline, factored for rung E).
fn register_audited_theorem(
    env: &mut Environment,
    name_str: &str,
    statement: Expr,
    proof: Expr,
    residues: &mut Vec<String>,
) -> Result<(), String> {
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &statement).map_err(|e| format!("check_type[{name_str}]: {e:?}"))?;
    }
    let decl_name = Name::from_string(name_str);
    env.add_decl(Declaration::Theorem {
        name: decl_name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    })
    .map_err(|e| format!("add_decl[{name_str}]: {e:?}"))?;
    match env.axiom_deps(&decl_name) {
        Some(residue) if residue.is_empty() => Ok(()),
        Some(residue) => {
            residues.extend(residue.iter().map(ToString::to_string));
            Ok(())
        }
        None => Err(format!("{name_str} not found after add")),
    }
}

/// RUNG E — check the LAUNCH-WRAPPER composition witness (depthless family):
/// register the mirror + interpreter, prove `memoAdequate`, then prove
/// `wrapAdequate` by `congrArg` composition. `claim` overrides the
/// conclusion's RHS — the fail-closed probe hook (an identity claim `= e` or
/// a swapped-eliminator claim is not def-eq → `KernelRejected`).
#[must_use]
pub fn check_expr_fold_wrap_refinement_claimed(
    ctors: &[TCtor],
    claim: Option<&Expr>,
) -> RefinementVerdict {
    let (mut env, names) = match build_expr_fold_env(ctors) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let mut residues: Vec<String> = Vec::new();
    match build_memo_adequate(&names, ctors) {
        Ok((st, pf)) => {
            if let Err(e) = register_audited_theorem(
                &mut env,
                &format!("{NS}.memoAdequate"),
                st,
                pf,
                &mut residues,
            ) {
                return RefinementVerdict::KernelRejected(e);
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("memoAdequate: {e}")),
    }
    match build_wrap_adequate(&names, claim) {
        Ok((st, pf)) => {
            if let Err(e) = register_audited_theorem(
                &mut env,
                "Trust.TrustIr.Refinement.expr_fold_wrap",
                st,
                pf,
                &mut residues,
            ) {
                return RefinementVerdict::KernelRejected(e);
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("wrapAdequate: {e}")),
    }
    if residues.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residues.sort();
        residues.dedup();
        RefinementVerdict::Residue(residues)
    }
}

/// RUNG E — the depth-family twin of
/// [`check_expr_fold_wrap_refinement_claimed`] (`memoAdequateD` +
/// `wrapAdequateD` at `∀ e d`).
#[must_use]
pub fn check_expr_fold_wrap_refinement_claimed_d(
    ctors: &[TCtor],
    claim: Option<&Expr>,
) -> RefinementVerdict {
    let (mut env, names) = match build_expr_fold_env_d(ctors) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let mut residues: Vec<String> = Vec::new();
    match build_memo_adequate_d(&names, ctors) {
        Ok((st, pf)) => {
            if let Err(e) = register_audited_theorem(
                &mut env,
                &format!("{NS}.memoAdequateD"),
                st,
                pf,
                &mut residues,
            ) {
                return RefinementVerdict::KernelRejected(e);
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("memoAdequateD: {e}")),
    }
    match build_wrap_adequate_d(&names, claim) {
        Ok((st, pf)) => {
            if let Err(e) = register_audited_theorem(
                &mut env,
                "Trust.TrustIr.Refinement.expr_fold_wrap_d",
                st,
                pf,
                &mut residues,
            ) {
                return RefinementVerdict::KernelRejected(e);
            }
        }
        Err(e) => return RefinementVerdict::KernelRejected(format!("wrapAdequateD: {e}")),
    }
    if residues.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residues.sort();
        residues.dedup();
        RefinementVerdict::Residue(residues)
    }
}

/// Cached honest launch-composition verdict (depthless) — the wrap witness is
/// folder-independent exactly like the fold witness, so one build serves
/// every wrapper over the same ctor table.
#[must_use]
pub fn check_expr_fold_wrap_refinement_cached(
    ctors: &[TCtor],
) -> (RefinementVerdict, std::time::Duration) {
    let key = format!("W:{ctors:?}");
    let cache =
        WITNESS_CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((v, d)) = guard.get(&key) {
            return (v.clone(), *d);
        }
    }
    let t0 = std::time::Instant::now();
    let verdict = check_expr_fold_wrap_refinement_claimed(ctors, None);
    let dt = t0.elapsed();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, (verdict.clone(), dt));
    }
    (verdict, dt)
}

/// Cached honest launch-composition verdict (depth family).
#[must_use]
pub fn check_expr_fold_wrap_refinement_cached_d(
    ctors: &[TCtor],
) -> (RefinementVerdict, std::time::Duration) {
    let key = format!("WD:{ctors:?}");
    let cache =
        WITNESS_CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((v, d)) = guard.get(&key) {
            return (v.clone(), *d);
        }
    }
    let t0 = std::time::Instant::now();
    let verdict = check_expr_fold_wrap_refinement_claimed_d(ctors, None);
    let dt = t0.elapsed();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, (verdict.clone(), dt));
    }
    (verdict, dt)
}

// ---------------------------------------------------------------------------
// RUNG E — the ADT-valued call transport twin (design §3.4 option (a)).
// ---------------------------------------------------------------------------

/// Register the `CallE` twin over the fold mirror: the inductive
/// `CallE.mk : Nat → Operand → TExpr → CallE` and the `callResultE` recursor
/// projection. The non-vacuous composition theorem is minted at the concrete
/// call site by [`check_call_return_instance_texpr`].
fn register_call_e(env: &mut Environment, names: &WitnessNames) -> Result<(), String> {
    use crate::trustir_anchor::TRUSTIR_OPERAND;
    let calle = format!("{NS}.CallE");
    let calle_mk = format!("{NS}.CallE.mk");
    let calle_rec = format!("{NS}.CallE.rec");
    let call_result_e = format!("{NS}.callResultE");
    let operand_ty = || cst(TRUSTIR_OPERAND);
    if env.get_inductive(&Name::from_string(&calle)).is_none() {
        let mk_ctor = Constructor {
            name: Name::from_string(&calle_mk),
            type_: Expr::pi(
                bd(),
                cst("Nat"),
                Expr::pi(bd(), operand_ty(), Expr::pi(bd(), texpr_ty(names), cst(&calle))),
            ),
        };
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&calle),
                type_: Expr::type_(),
                constructors: vec![mk_ctor],
            }],
        })
        .map_err(|e| format!("add_inductive(CallE): {e:?}"))?;
    }
    if env.get_const(&Name::from_string(&call_result_e)).is_none() {
        // callResultE = λ c. CallE.rec.{1} (λ_.TExpr) (λ callee arg ret. ret) c
        let rec = Expr::const_(Name::from_string(&calle_rec), vec![l1()]);
        let motive = Expr::lam(bd(), cst(&calle), texpr_ty(names));
        let minor = Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), texpr_ty(names), Expr::bvar(0))),
        );
        let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&call_result_e),
            level_params: vec![],
            type_: Expr::pi(bd(), cst(&calle), texpr_ty(names)),
            value: Expr::lam(bd(), cst(&calle), body),
            is_reducible: true,
        })
        .map_err(|e| format!("add_decl(callResultE): {e:?}"))?;
    }
    Ok(())
}

/// RUNG E — the per-call-site `callReturnInstanceE`: the TExpr-valued
/// transport instance at the concrete `CallE.mk <callee-id> <arg>`,
/// quantified over the callee-supplied return `ret : TExpr` and the contract
/// `post : TExpr → Prop`. The premise is the callee guarantee `post ret`; the
/// conclusion is `post (callResultE (CallE.mk id arg ret))`. Thus the kernel
/// rechecks the actual composition equation at this call site. The old
/// `P(callResultE c) → P(callResultE c)` identity carried no such semantic
/// content. `claimed_concl_pred` overrides the conclusion's predicate — the
/// fail-closed hook (a WRONG postcondition must NOT prove).
#[must_use]
pub fn check_call_return_instance_texpr(
    ctors: &[TCtor],
    callee_id: u64,
    arg: &crate::trustir_anchor::IrOperand,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let (mut env, names) = match build_expr_fold_env(ctors) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_e(&mut env, &names) {
        return RefinementVerdict::KernelRejected(e);
    }
    let calle_mk = format!("{NS}.CallE.mk");
    let call_result_e = format!("{NS}.callResultE");
    let post_ty = || Expr::pi(bd(), texpr_ty(&names), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(&calle_mk), [Expr::nat_lit(callee_id), arg.to_operand_expr(), ret])
    };
    // Type: ∀ (post : TExpr → Prop)(ret : TExpr),
    //   post ret → <pred> (callResultE (CallE.mk id arg ret)).
    let inst_ty = {
        let hyp = Expr::app(Expr::bvar(1), Expr::bvar(0));
        let concl_pred =
            claimed_concl_pred.cloned().map(|p| p.lift(3)).unwrap_or_else(|| Expr::bvar(2));
        let concl = Expr::app(concl_pred, Expr::app(cst(&call_result_e), call_at(Expr::bvar(1))));
        Expr::pi(bd(), post_ty(), Expr::pi(bd(), texpr_ty(&names), Expr::pi(bd(), hyp, concl)))
    };
    // Proof: λ post ret h. h. This is accepted only because the kernel reduces
    // `callResultE (CallE.mk id arg ret)` to that exact `ret`; a drifted
    // projection or conclusion predicate is rejected.
    let inst_proof = {
        let hyp_ty = Expr::app(Expr::bvar(1), Expr::bvar(0));
        Expr::lam(
            bd(),
            post_ty(),
            Expr::lam(bd(), texpr_ty(&names), Expr::lam(bd(), hyp_ty, Expr::bvar(0))),
        )
    };
    let mut residues = Vec::new();
    if let Err(e) = register_audited_theorem(
        &mut env,
        &format!("{NS}.callReturnInstanceE"),
        inst_ty,
        inst_proof,
        &mut residues,
    ) {
        return RefinementVerdict::KernelRejected(e);
    }
    if residues.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residues.sort();
        residues.dedup();
        RefinementVerdict::Residue(residues)
    }
}

/// Cached honest [`check_call_return_instance_texpr`] verdict (keyed on the
/// ctor table + the concrete pin — deterministic, input-pinned).
#[must_use]
pub fn check_call_return_instance_texpr_cached(
    ctors: &[TCtor],
    callee_id: u64,
    arg: &crate::trustir_anchor::IrOperand,
) -> RefinementVerdict {
    let key = format!("CE:{callee_id}:{arg:?}:{ctors:?}");
    let cache =
        WITNESS_CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((v, _)) = guard.get(&key) {
            return v.clone();
        }
    }
    let t0 = std::time::Instant::now();
    let verdict = check_call_return_instance_texpr(ctors, callee_id, arg, None);
    let dt = t0.elapsed();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, (verdict.clone(), dt));
    }
    verdict
}

// ===========================================================================
// Tests — the ZFC-nesting kernel validation + witness sanity (the recognizer
// is pinned against REAL MIR by tests/expr_fold_corpus.rs)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// The design-§3.1 ZFC-nesting decision, VALIDATED (deferred at rungs A
    /// and B): the kernel ACCEPTS a 2-type MUTUAL inductive block
    /// (`add_inductive` with two `InductiveType`s referencing each other), so
    /// flattening `ZFCSetExpr` into `TExpr` is a modeling CHOICE (single
    /// recursor, one motive), not a workaround for a kernel gap.
    #[test]
    fn mutual_two_type_inductive_block_registers() {
        let mut env = crate::trustir_anchor::trustir_env().expect("env");
        let a = "Trust.TrustIr.ExprFold.TestMutA";
        let b = "Trust.TrustIr.ExprFold.TestMutB";
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: Name::from_string(a),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor {
                            name: Name::from_string(&format!("{a}.leaf")),
                            type_: cst(a),
                        },
                        Constructor {
                            name: Name::from_string(&format!("{a}.wrap")),
                            type_: Expr::pi(bd(), cst(b), cst(a)),
                        },
                    ],
                },
                InductiveType {
                    name: Name::from_string(b),
                    type_: Expr::type_(),
                    constructors: vec![Constructor {
                        name: Name::from_string(&format!("{b}.pair")),
                        type_: Expr::pi(bd(), cst(a), Expr::pi(bd(), cst(a), cst(b))),
                    }],
                },
            ],
        };
        env.add_inductive(decl).expect("the kernel must accept a 2-type mutual inductive block");
        // Both recursors exist and the ctors typecheck end-to-end.
        let leaf = cst(&format!("{a}.leaf"));
        let val = Expr::app(
            cst(&format!("{a}.wrap")),
            Expr::apps(cst(&format!("{b}.pair")), [leaf.clone(), leaf]),
        );
        let tc = TypeChecker::new(&env);
        tc.check_type(&val, &cst(a)).expect("mutual ctor application typechecks");
    }

    /// A minimal 3-ctor table exercises the witness builder end-to-end
    /// without the fixture corpus (leaf + none + merge2 arms).
    fn mini_ctors() -> Vec<TCtor> {
        vec![
            TCtor {
                name: "BVar".to_string(),
                tag: 0,
                zfc: false,
                fields: vec![TField::Payload],
                arm: TArm::Leaf(LeafSlot::BVar),
            },
            TCtor {
                name: "SProp".to_string(),
                tag: 1,
                zfc: false,
                fields: vec![],
                arm: TArm::NoneArm,
            },
            TCtor {
                name: "App".to_string(),
                tag: 2,
                zfc: false,
                fields: vec![TField::Rec, TField::Rec],
                arm: TArm::Merge { children: vec![0, 1], binders: vec![false, false] },
            },
        ]
    }

    /// The mini table with a rung-D BINDER ctor (a Lam-like merge whose
    /// second child is folded at `dsucc d`) and a Map1 binder ctor.
    fn mini_ctors_d() -> Vec<TCtor> {
        let mut v = mini_ctors();
        v.push(TCtor {
            name: "Lam".to_string(),
            tag: 3,
            zfc: false,
            fields: vec![TField::Payload, TField::Rec, TField::Rec],
            arm: TArm::Merge { children: vec![1, 2], binders: vec![false, true] },
        });
        v.push(TCtor {
            name: "PathLam".to_string(),
            tag: 4,
            zfc: false,
            fields: vec![TField::Rec],
            arm: TArm::Map1 { child: 0, binder: true },
        });
        v
    }

    #[test]
    fn mini_witness_mints_modulo3() {
        assert_eq!(check_expr_fold_refinement(&mini_ctors()), RefinementVerdict::ProvenModulo3);
    }

    /// The memoAdequate machinery is GENUINE: a mini-table claim with swapped
    /// merge children must be KernelRejected (the mirror of the corpus-level
    /// probes, kept hermetic here).
    #[test]
    fn mini_forgery_swapped_children_rejected() {
        let honest = mini_ctors();
        let mut wrong = honest.clone();
        wrong[2].arm = TArm::Merge { children: vec![1, 0], binders: vec![false, false] };
        let rhs = probe_arm_rhs(&wrong, 2).expect("render");
        let mut claims: Vec<Option<Expr>> = vec![None; honest.len()];
        claims[2] = Some(rhs);
        assert!(matches!(
            check_expr_fold_refinement_claimed(&honest, &claims),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    // -----------------------------------------------------------------------
    // RUNG D — the depth-family witness (hermetic mini-table pins; the real
    // 33-ctor table is exercised by tests/expr_fold_corpus.rs).
    // -----------------------------------------------------------------------

    /// The depth interpreter + per-ctor theorems + memoAdequateD mint
    /// modulo 3 on a table with binder-marked merge AND map1 children.
    #[test]
    fn mini_depth_witness_mints_modulo3() {
        assert_eq!(check_expr_fold_refinement_d(&mini_ctors_d()), RefinementVerdict::ProvenModulo3);
    }

    /// THE rung-D forgery: claiming the binder child's IH at `d` where the
    /// honest minor has `dsucc d` is not def-eq → KernelRejected. (And the
    /// dual: claiming a plain child at `dsucc d`.)
    #[test]
    fn mini_depth_forgery_ih_at_wrong_depth_rejected() {
        let honest = mini_ctors_d();
        // Lam with the binder mark DROPPED (body IH at d).
        let mut wrong = honest.clone();
        wrong[3].arm = TArm::Merge { children: vec![1, 2], binders: vec![false, false] };
        let rhs = probe_arm_rhs_d(&wrong, 3).expect("render");
        let mut claims: Vec<Option<Expr>> = vec![None; honest.len()];
        claims[3] = Some(rhs);
        assert!(
            matches!(
                check_expr_fold_refinement_claimed_d(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "an IH claimed at d where the code folds at dsucc d must be KernelRejected"
        );
        // The dual: App with a binder mark ADDED (f IH at dsucc d).
        let mut wrong2 = honest.clone();
        wrong2[2].arm = TArm::Merge { children: vec![0, 1], binders: vec![true, false] };
        let rhs2 = probe_arm_rhs_d(&wrong2, 2).expect("render");
        let mut claims2: Vec<Option<Expr>> = vec![None; honest.len()];
        claims2[2] = Some(rhs2);
        assert!(
            matches!(
                check_expr_fold_refinement_claimed_d(&honest, &claims2),
                RefinementVerdict::KernelRejected(_)
            ),
            "an IH claimed at dsucc d where the code folds at d must be KernelRejected"
        );
        // Map1 binder dropped.
        let mut wrong3 = honest.clone();
        wrong3[4].arm = TArm::Map1 { child: 0, binder: false };
        let rhs3 = probe_arm_rhs_d(&wrong3, 4).expect("render");
        let mut claims3: Vec<Option<Expr>> = vec![None; honest.len()];
        claims3[4] = Some(rhs3);
        assert!(matches!(
            check_expr_fold_refinement_claimed_d(&honest, &claims3),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// Swapped merge children stay rejected in the depth family too.
    #[test]
    fn mini_depth_forgery_swapped_children_rejected() {
        let honest = mini_ctors_d();
        let mut wrong = honest.clone();
        wrong[2].arm = TArm::Merge { children: vec![1, 0], binders: vec![false, false] };
        let rhs = probe_arm_rhs_d(&wrong, 2).expect("render");
        let mut claims: Vec<Option<Expr>> = vec![None; honest.len()];
        claims[2] = Some(rhs);
        assert!(matches!(
            check_expr_fold_refinement_claimed_d(&honest, &claims),
            RefinementVerdict::KernelRejected(_)
        ));
    }
}

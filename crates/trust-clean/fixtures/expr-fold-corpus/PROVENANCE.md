# expr-fold-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

One hundred twenty-four real `-Ztrust-dump=mir:<dir>` dumps (77 rung-C originals
plus 27 rung-D additions plus 20 rung-E additions; never hand-transcribed) of the
**REAL clean-kernel Expr-fold SCC** (`first-party/clean/crates/clean-kernel/
src/expr/{subst.rs, visitor_opt.rs, mod.rs, kind.rs}`, byte-for-byte vendored
by the `../census-m6-cleankernel-2026-07-08/extract-foldmemo` census crate —
see ITS provenance for the file-level copy audit), compiled by the prebuilt
stage1 `trustc` (`rustc 1.99.0-dev (722ce062d 2026-07-11) (trustc)`) in
dump-only survey mode. One-command reproduction: `./regenerate.sh`; the
workflow-only integrity check is `./regenerate.sh --check-workflow`.

The stage1 extraction emitted 604 content-addressed JSON dumps. Regeneration
does not guess their filenames: it requires the checked-in 124-file inventory
to have 124 unique `.def_path` owners, joins each owner to exactly one fresh
dump, and stages the complete generation. `MANIFEST.sha256` binds every
checked-in filename to its bytes. `TOOLCHAIN.sha256` separately records exact
SHA-256 fingerprints and reported versions for Cargo, trustc, jq, and Python,
plus hashes of the target-selective rustc wrapper, regeneration script, and
corpus manifest. Tool fingerprints are checked both before and after
extraction, so an in-flight tool/script replacement aborts publication.

Regeneration runs under an `env -i` allowlist with isolated `HOME`,
`CARGO_HOME`, and `TMPDIR`; the controlled Cargo home may symlink only source
registry/git caches, never configuration or credentials. Dependency builds
stay verification-off and only the final `extract_foldmemo` target is
re-enabled through the target-selective wrapper.

Publication is a journaled same-filesystem transaction. Every staged JSON and
both manifests are fsynced before rename; the global transaction journal
records old/new corpus and toolchain hashes and makes recovery independent of
the process that started it. The manifest rename is the commit point, with
directories and the committed manifest fsynced before backups are removed.
Pre-commit/mixed states roll back; a complete post-commit state is retained;
ownerless staging/backup artifacts without a journal fail closed. Recovery
binds both transaction-directory names to the journal's run token, requires
real non-symlink directories, and validates the exact sorted 124-entry safe
manifest grammar before using any filename as a path.

The writer lock is a stable symlink to a fully initialized owner directory.
Ownership records a nonce plus PID and process-start identity (closing PID
reuse); owner metadata is initialized and fsynced under a temporary name before
its directory is atomically published. After acquiring the public lock, a run
reaps only dead, unreferenced owner artifacts and leaves live contenders alone.
Stale takeover installs an internal claim without ever removing the public lock
name. Lock/claim creation invokes `symlink(2)` directly (so an existing
directory cannot turn acquisition into an accidental child link), and resolved
owner/claim targets must be reserved direct children of this corpus directory
before takeover, mutation, or deletion. `./regenerate.sh --check-workflow`
forces lock/recovery interleavings, stale-owner/orphan recovery,
unmanaged-target and directory-following adversaries, transaction recovery,
environment poisoning, wrapper ordering, tool/manifest checks, and
mixed-generation rejection, then verifies that its lock-owner/claim/temporary
artifacts are gone.

The integration tests consume the corpus through one immutable
`CorpusSnapshot`: one strictly sorted two-field corpus-manifest read selects all
124 bodies, every hash and owner is verified, the raw JSON inventory must match
exactly, and duplicate owners are rejected. The loader also requires the exact
seven-entry toolchain schema, checks the current wrapper, regeneration script,
and corpus-manifest hashes, and re-reads both manifests and both repository
scripts byte-for-byte before publishing the snapshot. All root/co-member
lookups for a recognition attempt therefore come from one generation even if a
publisher commits concurrently.

The manifest and filename hashes continue to authenticate the original raw
wire bytes. Thirty-eight of those pre-P4 dumps contain historical extraction
metadata defects: compact recursive type back-references, omitted faithful
default-enum markers, or one of three ptr-to-u64 constants erased to
`OpaqueConst`. The production decoder applies one fail-closed transaction per
exact `(raw SHA-256, def_path)` profile. Each transaction pins exact type or
statement coordinates, checks back-reference equivalence / complete enum-table
coherence / the exact u64 assignment shape, and publishes the canonical value
only after VCgen validation and all assignment types agree. The corpus test
independently observes 105 raw assignment failures across exactly 38 files,
requires exactly 38 canonical changes, revalidates all 124 decoded bodies, and
proves a one-byte drift revokes every repair. Consequently, raw SHA-256 values
remain provenance identities while `VerifiableFunction::content_hash()` pins
refer to the authenticated decoded representation.

This is RUNG C of the structural-fold lane
(`docs/design/2026-07-10-structural-fold-lane.md` §5 Rung C): the DEPTHLESS
MEMOIZED Expr folders, certified as an SCC unit by
`crates/trust-clean/src/trustir_fold_expr.rs`. Consumed by
`tests/expr_fold_corpus.rs` through the production gate
(`diagnose_fully_faithful_gate_with_bodies` — the same gate
`prove_one_function` evaluates).

## The members

| dump group | role | expected outcome |
|---|---|---|
| `FVarSubst::fold_expr_opt` (+ `{closure#0}`) | THE rung-C flip row: depthless memoized wrapper, `(expr, 0u32)` key pair | **FULLY_FAITHFUL via trust-ir** (rung-C arm: memo peel under `memoAdequate`, 33-ctor flattened `TExpr` witness, leaf slots = `fold_fvar_opt` override (itself FF) + 4 literal-`None` defaults, `should_descend` chain re-certified standalone) |
| `LevelParamSubst::fold_expr_opt`, `LevelParamSubstSlice::fold_expr_opt` (+ closures) | same shape, HOSTAGE rows | recognize (`sem_expr_fold_shape_of` Ok, overrides = {Sort, Const}) but the GATE declines: `fold_sort_opt` calls `Level::substitute_map` (recursive `Option<Level>` fold — rung-E callee territory), `fold_const_opt` carries the `Iterator::map`+`collect::<SmallVec>` residue — no lane certifies them, so the rows stay honestly short of FULLY_FAITHFUL (design §5's "minus any hostage to `fold_const_opt`'s `Iterator::collect` residue") |
| `Instantiator::fold_expr_opt` | the depth-THREADING contrast row (memo key = `cp (*_1).f1`, a depth FIELD read) | NAMED decline `fold_memo::depth_key_unsupported` in the rung-C arm; recognized by rung D and currently FULLY_FAITHFUL after the leaf-assert-unhostage follow-up below |
| `Abstractor::fold_expr_opt` | inline `HashMap` memo (not the `FoldMemo` get/put idiom) | NAMED decline (wrapper shape) |
| `FoldMemo::{get,put}` | the memo internals: `(AddressOf(*expr) → opaque u64, depth)` key + `HashMap::get`/`Option::cloned` / `clone`+`insert`+return-result | fingerprinted (P-ADDR / P-CLONE positions; raw extraction used `OpaqueConst`, while the authenticated canonical form is exact unsigned `OpaqueScalar<64>`, with the `AddressOf` adjacent — folded into P-ADDR's text) |
| `expr::stack_safe` | the P-STACK trampoline (generic two-literal `maybe_grow` forwarding) | fingerprint target (rung-B matcher reused) |
| `ExprFolderOpt::fold_expr_opt_inner{,_full}`, `_extensions`, `_zfc`, `fold_zfc_set_expr_opt`, `fold_binder_body_opt`, the 5 leaf defaults (+ all their closures) | the GENERIC default-dispatch SCC co-members (dumped ONCE, polymorphically; specialized by folder-context callee resolution) | walked arm-by-arm: 25-tag vetted switch, per-arm strict-subterm folds, `merge2/3/4`/`Option::map` rebuilds, the zfc inline merges; every drift declines by name |
| `merge2/3/4` (+ closures) | the sharing-preserving rebuild combinators | fingerprinted against the `mergeKE` model (any-some cascade, `map_or_else` picks with `\|\| old.clone()` closures + `Arc::new` ZST, `FnOnce::call_once(make)`, `ek`, `Some`) |
| `Expr::kind`, `expr::kind::ek`, `Expr::from_kind`, `<Expr as Clone>::clone` | accessor/rebuild/clone pins (kind-field passthrough; META ERASED — the witness is the kind-tree property tier) | fingerprinted |
| `should_descend` overrides ×3 + `has_fvar_quick`/`ExprMeta::has_fvar` + `has_level_param_quick`/`ExprMeta::has_level_param` | the G-slot implementations + their call chains | re-certified STANDALONE (finite tri-color DFS, content-hash memoized, cycles fail closed, order-free) |
| `FVarSubst::fold_fvar_opt`, `LevelParamSubst{,Slice}::{fold_sort_opt, fold_const_opt}` (+ closures) | the leaf-slot overrides | fvar: FF (adt_return_opaque lane); sort/const: the honest blockers (see hostage rows) |

## MIR facts the recognizer is pinned against (read off these real dumps)

* All three depthless wrappers carry the LITERAL `const 0u32` depth in BOTH
  `FoldMemo::get` and `FoldMemo::put`; `Instantiator`'s wrapper instead copies
  `(*_1).f1` (the depth field) — the named rung-D decline is pinned on real
  MIR, not a synthetic.
* Trait-dispatch callees render as the GENERIC trait path
  (`expr::visitor::opt::ExprFolderOpt::<method>`) even in CONCRETE impl
  bodies; inherent methods render resolved. The recognizer therefore resolves
  trait callees by folder context: an override DUMP exists ⇔ the impl
  overrides (every local concrete fn is dumped), else the generic default
  body (also dumped) is the resolution.
* `ExprKind` has 25 variants (tags 0..=24, `exhaustive_enum_unreachable`
  vetted); `ZFCSetExpr` has 9 (tags 0..=8, vetted). `fold_expr_opt_extensions`
  and `fold_expr_opt_zfc` are PARTIAL dispatches whose `otherwise` is the
  `unreachable!()` panic chain (diverging; verified as such) — reachable only
  through inner_full's covered tags, which the composed walk verifies.
* Zero-sized callable constants now render as `ConstValue::CallableItem` with
  an exact diagnostic def-path, `CallableKind`, and both 64-bit components of
  rustc's collision-checked `DefPathHash` (stable crate id + local hash).
  Recognition requires all four fields. Historical identity-less
  `ConstValue::Unit` values, a wrong kind, either changed hash component, a
  same-shaped callback substitution, and an App-for-`Arc::new` substitution
  all decline. The corpus exhaustively contains 30 occurrences of exactly 16
  identities: App once, 14 constructor closures once each, and `Arc::new` 15
  times. Every closure additionally resolves to its exact co-member body,
  whose `VerifiableFunction::content_hash()` is pinned before its constructor
  behavior is walked. This retires P-CTOR-ZST rather than weakening it.
* `Expr::kind(..)` is a real CALL in the dispatch bodies (`&(*_1).f0`
  accessor, fingerprinted); the strict-subterm chain is
  param → kind-field → `Downcast(v).Field(f)` → `Deref::deref` (P-ARC-DEREF
  type pins on `&Arc<..Expr..>` → `&Expr`).
* Drop-flag locals (`const bool` writes steering conditional drops) appear on
  HAPPY paths in `merge*`/zfc bodies; the walker whitelists exactly the
  locals that are const-bool-assigned and switch-consumed, fail-closed.
* Leaf/G purity is alias- and provenance-aware across local helper calls.
  Shared references copied out of the folder detach only when their logical
  payload is visibly immutable or its complete extracted type graph is pinned.
  `LevelParamSubst::subst`'s HashMap graph is pinned at
  `c759217cf7c58d1bef4169ee22d4d920df63dd4611d5897e3ed81edae0a76973`:
  allocator raw-pointer bookkeeping is not mistaken for logical mutation,
  while Cell/UnsafeCell/atomic/lock/type/layout drift invalidates the pin.
  Mutable/raw aliases, aggregate laundering, pointer→integer→pointer casts,
  recursive helper mutation, and unproved alias escapes all decline
  `fold_memo::impure_state`.

### Callable identity ledger

The serialized hash components below are exactly 16 lowercase hexadecimal
digits. Closure body hashes are the production
`VerifiableFunction::content_hash()` values; function-item rows have no
co-member body in this corpus.

| occurrences | exact def-path | kind | stable crate id | local hash | co-member body hash |
|---:|---|---|---|---|---|
| 1 | `expr::kind::ExprKind::App` | `fn_def` | `7508ca85e6100c00` | `bc8c212df299ed62` | — |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full::{closure#5}` | `closure` | `7508ca85e6100c00` | `6b7b4c5cfd70ffdd` | `b331095a3a727ace9235cc5212be3940ae0d3f867077d4e8656904bc4aad78f6` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#0}` | `closure` | `7508ca85e6100c00` | `5fdcc31917fb4403` | `cadac6b6f1303466d22529d2c63443b57606adcae2fdea48a95b2e9e970ffd04` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#1}` | `closure` | `7508ca85e6100c00` | `e564c15855b3eedd` | `c2694fbf36863dec2022e5cf7e4c57378698d5b9138a29d3f58590053c51c001` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#2}` | `closure` | `7508ca85e6100c00` | `6d644c3f403ba3dc` | `70f1df0d0f7aac15a36d5597da9f60bac41f9a7ff95fc26b0bdbee56251d52a2` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#3}` | `closure` | `7508ca85e6100c00` | `f62ee26e807b71f2` | `b08f89bb120a64755aef6fc1aa89e61f47671f7d6ae473a5817f90d1a5b53c25` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#4}` | `closure` | `7508ca85e6100c00` | `57da621320568a7c` | `5fbdd97953675930e72f57a343a2cc051abfd391ede3d798ef65aea0b8c3f3b2` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#5}` | `closure` | `7508ca85e6100c00` | `73d8d0b61d768ad6` | `825f339ef2d305b30147b6eda666a45c3976ccfe167e0b14db618ea0b7236712` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#0}` | `closure` | `7508ca85e6100c00` | `4de23e93e74105f5` | `8897f37073ffa74c4f2d617ff82eccf57bef04fe5455fd3dd76a289b1e3fb411` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#1}` | `closure` | `7508ca85e6100c00` | `f4556b7b11df89e4` | `fdefa28216db730415139536f84a8e23b030d0bca8c89f669913df13fa5cf2c9` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#2}` | `closure` | `7508ca85e6100c00` | `acc35f8aa986b6c6` | `9e6d2ff4bbe388fde7c95a6ec565629efbb5862c11fa9968182ccf5a396e9fc1` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#0}` | `closure` | `7508ca85e6100c00` | `249a80707f2bb911` | `08c88099c46a7a6d28ea2b1c754415fecfbdb09762eb4af00e9b66a56178040a` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#3}` | `closure` | `7508ca85e6100c00` | `5cf869889fb25a13` | `5264cc84b793060a7386453510338dd508157f0e66944adee554da694e227150` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#4}` | `closure` | `7508ca85e6100c00` | `83215fd4b3fd48f4` | `a90669d59b46f70a5cab76e19d9ad1783566af78d311fb606e7ef25b56b6c42f` |
| 1 | `expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#9}` | `closure` | `7508ca85e6100c00` | `568dd947806e692e` | `0dbd990ce9a09aa8f37e30f061666d90b9928ed77d59d093aa7dbf1c46cc9d1c` |
| 15 | `std::sync::Arc::<T>::new` | `fn_def` | `9d72b10b12841225` | `e31a916e7093729f` | — |

## Honesty notes

* Premises carried by the flip row (module doc of `trustir_fold_expr.rs`):
  P-ACYC (now guarded by an executable dump type-graph check plus a source
  `forbid(unsafe_code)`/Weak/interior-mutability tripwire), P-ARC-DEREF,
  P-STACK, P-ADDR (as the `memoAdequate` hypothesis'
  real-world justification), P-CLONE, P-OPT-STD. P-CTOR-ZST is retired by the
  callable identity and co-member body pins above; it is no longer carried.
* The witness is MODEL-ONLY (the `trustir_adt.rs` tier) and covers the
  KIND-TREE component of values — `ExprMeta` is ERASED (recomputed cache;
  separately exercised by the FF `ExprMeta` rows).
* The ZFC-nesting decision (design §3.1, deferred twice): FLATTENED —
  `TExpr` has 33 ctors (25 − ZFCSet + 9 zfc) and stays a single non-mutual
  inductive; the kernel's 2-type mutual `add_inductive` was separately
  validated (`mutual_two_type_inductive_block_registers` in
  `trustir_fold_expr.rs` tests), making flattening a modeling CHOICE.

## RUNG D additions (2026-07-11)

Twenty-seven more dumps from the SAME extraction recipe (selected from the
fresh 604-dump run, same `extract-foldmemo` crate, same prebuilt stage1
`trustc` — `rustc 1.99.0-dev (722ce062d 2026-07-11) (trustc)`), covering the
DEPTH-THREADING folders (design §5 Rung D):

| dump group | role | expected outcome |
|---|---|---|
| `Instantiator`/`MultiInstantiator`/`Lifter`/`Lowerer` `fold_expr_opt` (+ `{closure#0}`) | the depth-key `FoldMemo` wrappers (get key = `cp (*_1).f_depth`; put key = the PRE-call copy taken before `stack_safe`) | recognize as rung-D SCC units |
| `Abstractor::fold_expr_opt` (+ `{closure#0}`) | the INLINE-HashMap memo idiom: key tuple `(AddressOf(*expr)→opaque u64, depth)` built once; raw extraction used `OpaqueConst`, authenticated decoding restores exact unsigned `OpaqueScalar<64>`; hit → `cached.clone()` whole; miss → insert(key, result.clone()), evicted `Option` dropped UNREAD, RESULT returned | recognizes as the rung-D inline SCC unit |
| ×5 `fold_binder_body_opt` | the save/`checked_add_u32(+1)`/call/restore overrides — the C-family SCC co-member rows | Abstractor + Lifter: **FULLY_FAITHFUL** in the original rung-D increment; Instantiator joins them in the leaf-assert-unhostage follow-up; MultiInstantiator + Lowerer remain hostage with their wrappers |
| ×5 `should_descend`, `Abstractor::{fold_bvar,fold_fvar}_opt`, `Lifter::fold_bvar_opt` | G slots + the certifiable leaves (opaque-chain ADT-return lane) | certified standalone (gate conjunct (c)) |
| `Instantiator`/`MultiInstantiator`/`Lowerer` `fold_bvar_opt` | the HONEST BLOCKER leaves: `lift_at` (recursive fold callee) + undischarged `idx−1`/`vals[i]` overflow/bounds asserts; Lowerer's REACHABLE debug-assert panic arm | NOT certified in the original rung-D increment — their SCCs stayed hostage BY NAME (`leaf_uncertified`); the opaque-total-slot alternative is REJECTED. **SUPERSEDED for `Instantiator` by the leaf-assert-unhostage increment (next row).** |
| **LEAF-ASSERT-UNHOSTAGE (2026-07-11)**: `Instantiator::fold_bvar_opt` | its `match idx.cmp(&self.depth)` dumps as the `__trust_total_clone`-sentinel `Ord::cmp` + `Discriminant` + exhaustive 3-tag `SwitchInt` (Less=255/Equal=0/Greater=1, read from the dump's own `std::cmp::Ordering` type info), with one `CheckedSub(idx,1)` + Overflow(Sub) `Assert` on the Greater arm and the `lift_at`/`bvar` calls as chain steps | **FULLY_FAITHFUL** via the ORDERING-DISPATCH OPAQUE-CHAIN lane: the Assert's VC is refuted modulo 3 under the guard-implied `idx > depth` fact. P-ORD-CMP is licensed only for the exact def-path `<expr::subst::Instantiator<'_> as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt`, authenticated decoded content hash `b278bfb4d47462acaacc8863d4262cf43b536dd3881b74c69f5a8944c08c1c10` (the raw wire SHA remains `ffa548068446c6a5f1eb6b17b2d17c55095a6c1d3e7f1efb570b74a5f7570b09`), exactly one safety VC, and exact serialized `(VcKind, Formula)` hash `fb3f47f3eda65a4b79ba3120f5c3e8017cf0d778b887a354fbd94431df808ed9`; complete block/type/tag/immutability checks remain defense in depth. No generic fact is injected. `lift_at`/`bvar` are universally bound steps with no value claim, and the SCC's wrapper + binder row flip through unchanged rung-D machinery. `MultiInstantiator` does NOT follow: its `self.depth + n` Add-overflow asserts are genuinely satisfiable (`depth = u32::MAX ∧ n ≥ 1` panics the real code), so it stays `leaf_uncertified` with Lowerer. |
| `expr::checked_add_u32` | the P-SAT-ADD fingerprint: exact forwarding to `core::num::<impl u32>::saturating_add` — the real depth successor is the u32-SATURATING successor (the witness keeps `dsucc` ∀-quantified; no unbounded `d+1` claim) | fingerprinted |
| `Expr::loose_bvar_range` + `ExprMeta::loose_bvar_range` | the depth-folder `should_descend` chains' callees (mirror of the `has_fvar_quick` chain) | certified standalone |

MIR facts the rung-D recognizer is pinned against (read off these dumps):

* All four `FoldMemo` depth wrappers are block-identical up to the depth
  field index (Instantiator/MultiInstantiator: field 1; Lifter/Lowerer:
  field 0 — the `start` counter IS the memo key, per the folder's own
  SOUNDNESS comment). The put's depth operand is the PRE-call copy
  (`_10 = cp (*_1).fD` before the closure aggregate) — a post-call re-read
  is declined as a stale-depth channel even though the restore discipline
  would make it equal.
* All five binder-body overrides are the EXACT 3-block
  save/inc/call/restore shape; the recursion callee renders as the GENERIC
  trait path `ExprFolderOpt::fold_expr_opt` (folder-contextual resolution =
  the folder's own wrapper override — the SCC edge).
* `Abstractor`'s wrapper carries unwind-noise blocks (`Drop(_14) → Resume`)
  — tolerated fail-closed (statement-free Drop/Resume chains only); its
  happy-path evicted-value `Drop(_16)` is pinned, and the evicted local is
  audited UNREAD across the whole body.

## RUNG E additions (2026-07-11)

Twenty more dumps from the SAME extraction recipe (fresh 538-dump run, same
`extract-foldmemo` crate, same prebuilt stage2 `trustc`), covering the
G-FAMILY WRAPPERS (design §3.4 + §5 Rung E; attack-plan family G):

| dump group | role | expected outcome |
|---|---|---|
| `subst_fvar`, `lift_at`, `abstract_fvar_at` | folder-LAUNCH wrappers over CERTIFIED SCCs (FVarSubst / Lifter / Abstractor): [optional `== 0` early-clone guard +] fresh-memo folder build + the pinned generic `fold_opt_or_clone` delegation | **FULLY_FAITHFUL** (option (b) inlining + `wrapAdequate`/`wrapAdequateD`) |
| `lift`, `lift_from`, `abstract_fvar` | pure ADT DELEGATES to the launch wrappers above | **FULLY_FAITHFUL** with the callee in the callees-first registry (option (a): the TExpr-valued `CallE`/`callResultE` transport twin); NOT FF with an empty registry — registry dependence pinned both ways |
| `Abstractor::new` | the fingerprinted folder ctor (`HashMap::new` + struct literal) | fingerprinted (P-OPT-STD; the ctor-form launch's field map source) |
| `Expr::fold_opt_or_clone` (+ `{closure#0}`) | the GENERIC driver, dumped once: `fold_expr_opt(folder, self)` + `unwrap_or_else(|| self.clone())` (closure captures exactly `self`; body = capture read + `Clone::clone`) | fingerprinted (the `wrapAdequate` composition's P-OPT-STD/P-CLONE positions) |
| `instantiate_at`, `instantiate_level_params_map` | launch shapes; at the banked wip BOTH were hostage SCCs | **TAKEOVER UPDATE (2026-07-12):** `instantiate_at` is **FULLY_FAITHFUL** — main's leaf-assert landing (P-ORD-CMP ordering-dispatch lane) certified the Instantiator SCC, so the launch arm now composes with it unchanged. `instantiate_level_params_map` RECOGNIZES and stays hostage (`leaf_uncertified`: LevelParamSubst's `fold_sort/const_opt` leaves) |
| `instantiate` | delegate to `instantiate_at` | **TAKEOVER UPDATE (2026-07-12): FULLY_FAITHFUL** with its callee in the callees-first registry (the callee now certifies); `fold_wrap::callee_unresolved` with an empty registry — the registry-dependence pin |
| `instantiate_rev` | slice guards (`is_empty`, `len == 1` + bounds-checked `&vals[0]`) before the launch | `fold_wrap::launch_shape` (outside the pinned vocabulary) + MultiInstantiator hostage anyway |
| `lower_loose_bvars` | `Option<Expr>`-returning launch over the hostage Lowerer + the `has_loose_bvar_in_range` pre-call | `fold_wrap::signature_unsupported` (named; doubly hostage) |
| `instantiate_level_params`, `instantiate_level_params_direct` | `iter().cloned().collect::<HashMap>()` / `SMALL_LEVEL_PARAM_SUBST_THRESHOLD` split + slice-folder launch | non-FF (the acknowledged `Iterator::collect` residue + LevelParamSubst(Slice) leaf hostages) |
| `has_loose_bvar`, `has_loose_bvar_in_range` | Bool-returning (the NOT-YET-CERTIFIED Expr-scale bool fold); `has_loose_bvar` additionally carries a GENUINELY SATISFIABLE `idx + 1` u32-overflow Assert (no bound on `idx`) | `fold_wrap::signature_unsupported` (named); the overflow VC blocks FF on the safety axis regardless of any future bool-fold lane |
| `collect_constants`, `collect_constants_into` | HashSet-returning accumulator-lane wrappers over the NOT-YET-CERTIFIED Expr-scale accumulator fold | `fold_wrap::signature_unsupported` (named) |

MIR facts the rung-E recognizer is pinned against (read off these dumps):

* `FoldMemo::default()` renders as the ZERO-ARG `__trust_total_clone`
  derived-total sentinel with the dest local's declared type =
  `expr::subst::FoldMemo` — the fresh-empty-memo start (P-ADDR's trivially
  sound oracle state; P-OPT-STD for the std ctor).
* The folder Aggregate names the folder type AND the folder local's DECLARED
  type carries the field list — the recognizer pins both (name equality +
  per-field operand/type compatibility), which is exactly what kills the
  wrong-denotation forgery (an aggregate renamed to a different folder
  declines `fold_wrap::folder_mismatch` on the declared-type disagreement).
* The generic driver's fold call renders as the GENERIC trait path
  `ExprFolderOpt::fold_expr_opt` — the wrapper→concrete-row edge exists
  ONLY through the wrapper's own folder aggregate (why option (b) inlining
  is structurally forced for the launch family).
* The three launch wrappers' folder-struct field spellings inside the
  wrapper dumps are COMPACTED (`FVarSubst.replacement`'s `Expr` carries a
  `Datatype("expr::kind::ExprKind", [])` back-reference where the parameter
  occurrence carries the full flattened Adt) — the PI-ARITY ambiguity
  channel that kept `subst_fvar`/`instantiate_at`/`instantiate_rev`
  NOT_GROUNDED. The original rung-E run reconstructed the richest same-name
  spelling and reported all three as ground + inhabit, but SF-2 supersedes
  that result: the empty Datatype leaf has no canonical identity after generic
  arguments are erased, so it cannot authorize a richer Adt spelling. Current
  `collect_adt_compaction_defs`/`resolve_adt_compaction` leaves the mismatch
  incomparable for opaque ambiguity collapse. The historical grounding
  result must be remeasured on the SF-2-safe tree. Full recursive-Datatype
  definition/back-reference resolution remains a separate, occurs-checked
  lane and is not disabled by this restriction.

## Generation-ledger repair at the rung-E takeover (2026-07-12)

The rung-E takeover merge (banked branch `worktree-agent-a908d6a9133257c95`
@ cc51103af5 onto main @ 6777a502e1) joined two histories that each changed
this corpus's integrity surface:

* The banked rung-E branch added the 20 wrapper dumps above. It predates the
  manifest machinery entirely (its base is rung-D-era main, where
  `MANIFEST.sha256`/`TOOLCHAIN.sha256` did not exist), so the merged corpus
  had 124 JSONs against a 104-entry manifest.
* Main's `MANIFEST.sha256`/`TOOLCHAIN.sha256`/1164-line `regenerate.sh`
  arrived in merge commit 476a4e2a89 ("Merge origin/main and harden the
  Trust toolchain") — and arrived BORN INCONSISTENT: that evil merge
  committed a `regenerate.sh` hashing
  `40354b406a455bdf18a6547a95c05aa87a75c54cedd33706050da24d7db3838`* while
  recording `15a21519…` for `regeneration_script` (a hash matching no
  committed version of the script; present in NEITHER merge parent). Every
  `expr_fold_corpus` test has therefore been failing AT LOAD on main since
  476a4e2a89 — a pre-existing main regression surfaced (not caused) by the
  takeover, refuted here rather than worked around.

Repair, all three files regenerated together (2026-07-12):

* `MANIFEST.sha256` rebuilt over the full 124-file inventory (plain
  SHA-256, bytewise-sorted filenames — the loader's own format).
* `regenerate.sh`'s `EXPECTED_INVENTORY` 104 → 124 (the only edit).
* `TOOLCHAIN.sha256`: `regeneration_script` and `corpus_manifest` entries
  re-recorded against the committed bytes. The other five entries are
  UNCHANGED — `rustc_wrapper` and the tool fingerprints verified intact.
  Note the pinned `trustc` (`bff86a49…`, `722ce062d 2026-07-11`) no longer
  matches the deployed `build/host` toolchain (`8e74b3bab 2026-07-10`,
  which lacks `-Ztrust-dump=mir:<dir>` entirely — the build tree was swapped
  after the census sessions); the pin correctly records the binary that
  PRODUCED the dumps, and any future regeneration will re-record it.

(*full hash in `git log`; line wrapped here.)

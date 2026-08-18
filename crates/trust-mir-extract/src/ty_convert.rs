// trust-mir-extract/ty_convert.rs: Convert rustc Ty to trust-types Ty
//
// Maps rustc's rich type system to our simplified verification types.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: enum-disc-full-native — `TagEncoding`/`Variants` classify an enum's
// discriminant layout. Same import path the compiler uses in
// `rustc_mir_transform/src/check_enums.rs:1` and `rustc_codegen_ssa`.
use rustc_abi::{TagEncoding, Variants};
use rustc_middle::ty::{self, TyCtxt, TyKind, TypeVisitableExt};
use trust_types::fx::FxHashMap;
use trust_types::{FnSig, Ty as TrustTy};

// verifier-perf: original budget restored. An earlier patch bumped
// nodes 4096 → 65536, but that interacted badly with the alias-normalize
// path — more types reached normalization, each invoking the trait
// solver, which then exceeded rustc's default 128 recursion limit while
// compiling crates like `typenum` that have deeply nested `UInt<…>`
// bounds. Revisit with a separate "skip normalize when bound likely to
// recurse" heuristic before raising again.
const MAX_TYPE_LOWERING_DEPTH: usize = 64;
const MAX_TYPE_LOWERING_NODES: usize = 4096;

// ── verifier-perf: PRODUCED-tree-size budget for type lowering ──────────────
//
// `remaining_nodes` (above) bounds the COUNT of distinct `convert_ty_inner`
// CALLS, but the memoization cache returns a `cached.clone()` WITHOUT charging,
// and `lower_enum_adt` DUPLICATES every variant field into the flattened
// `fields` view (`field_ty.clone()`) on top of the per-variant lists. So the
// SIZE of the PRODUCED `TrustTy` tree is not bounded by `remaining_nodes`: the
// kernel's mutually-recursive `Expr`/`ExprKind`/`Name` enums (each lowered once,
// then cloned into many parents) assemble a ~464 MB `Ty::Adt` tree, driving RSS
// to tens of GB and OOM-killing the verifier DURING EXTRACTION — upstream of all
// VC-gen / bundle bounds. This is the actual `build_ind_app`/`ProofCert::clone`
// stall: it is in `trust_mir_extract::ty_convert`, not in trust-vcgen.
//
// FIX: meter the cumulative node count of every PRODUCED subtree (charged for
// freshly-lowered trees AND for cache-hit clones, since the clone materializes
// the same memory). Once the cumulative produced size for ONE function's type
// lowering crosses the budget, every subsequent lowering returns the cheap
// fail-closed recursive-ADT `Unsupported` marker instead of assembling more fat
// tree. The marker is the SAME `Ty::Unsupported { kind: "TyKind::Adt", detail:
// "recursive…" }` shape this module already produces for recursive ADTs, so a
// degraded function is byte-identical to the pre-existing recursive-ADT path.
//
// SOUNDNESS (paramount): DROP-ONLY. A function whose types fit the budget is
// lowered byte-identically to baseline. A function over the budget has its fat
// types replaced by the fail-closed `Unsupported` marker, which carries NO
// modeled SMT sort — so every panic-able USE of such a value still fails closed
// at its use site (`place_sort` stays `None`), and no arithmetic/bounds/divzero
// VC is emitted for it. It can only LOSE proofs for that one function, never
// manufacture a false PROVE and never a guaranteed-violation. Overridable via
// The bound is a deterministic production constant so extraction cannot vary
// with process-global environment state.
//
// DEFAULT sizing: empirically, clean-kernel's recursive `Expr`/`ExprKind`/`Name`
// cluster drives peak verifier RSS ROUGHLY linearly in this budget — measured ~7.8
// GB at 5_000 (COMPLETES) vs ~32 GB (OOM) at 200_000. 8_000 keeps the peak in a
// ~10-13 GB band that completes with comfortable margin on a 48 GB host while
// retaining more datatype-field precision than 5_000. An ordinary function's whole
// declared-type set is well under this (a few hundred nodes), so ONLY the
// pathological recursive-enum cluster is ever degraded.
const MAX_TYPE_LOWERING_PRODUCED_NODES: usize = 8_000;

/// Total structural-node count of a produced `TrustTy`, short-circuited at `cap`
/// so a huge tree costs O(cap), not O(size). This is the real memory cost the
/// caller pays to retain/clone the lowered type.
fn produced_node_count(ty: &TrustTy, cap: usize) -> usize {
    fn go(ty: &TrustTy, cap: usize, acc: &mut usize) {
        if *acc >= cap {
            return;
        }
        *acc += 1;
        match ty {
            TrustTy::Ref { inner, .. } => go(inner, cap, acc),
            TrustTy::RawPtr { pointee, .. } => go(pointee, cap, acc),
            TrustTy::Slice { elem }
            | TrustTy::Array { elem, .. }
            | TrustTy::SymArray { elem, .. } => go(elem, cap, acc),
            TrustTy::Tuple(tys) => tys.iter().for_each(|t| go(t, cap, acc)),
            TrustTy::Adt { fields, variants, .. } => {
                for (_, t) in fields {
                    go(t, cap, acc);
                }
                for v in variants {
                    for (_, t) in &v.fields {
                        go(t, cap, acc);
                    }
                }
            }
            // Lever A: charge a datatype's variant-field nodes so the budget
            // still bounds a `Ty::Datatype` tree (a by-name ref is empty and
            // costs just the `+1` leaf above).
            TrustTy::Datatype { variants, .. } => {
                for (_, fs) in variants {
                    for (_, t) in fs {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Closure { upvars, .. } | TrustTy::Coroutine { upvars, .. } => {
                upvars.iter().for_each(|t| go(t, cap, acc));
            }
            _ => {}
        }
    }
    let mut acc = 0;
    go(ty, cap, &mut acc);
    acc
}

/// Deterministic produced-tree-size budget. Proof extraction must not depend on
/// ambient process environment: crossing the bound changes a type to an
/// explicit fail-closed marker and therefore changes the obligation inventory.
fn produced_node_budget() -> usize {
    MAX_TYPE_LOWERING_PRODUCED_NODES
}

/// The cheap fail-closed leaf returned once the produced-node budget is spent —
/// the SAME recursive-ADT `Unsupported` marker this module already produces for
/// genuinely recursive ADTs (load-bearing `detail.starts_with("recursive")`).
fn produced_budget_degraded_leaf() -> TrustTy {
    TrustTy::Unsupported {
        kind: "TyKind::Adt".to_string(),
        detail: "recursive ADT (degraded: type lowering exceeded produced-node budget)".to_string(),
    }
}

/// A BY-NAME recursive-datatype reference (Lever A): an empty-`variants`
/// `Ty::Datatype` whose only content is the referent's name. Emitted at a
/// recursive field position so the back-edge has a MODELED SMT sort
/// (`Sort::Datatype { name, constructors: [] }` resolves to the definitional
/// occurrence's declared datatype at declare time) — instead of the opaque
/// `Unsupported` that forced every projection/match through a recursive ADT to
/// Unknown. The defining occurrence (the outer, fully-lowered type) carries the
/// full structure. SOUNDNESS: a datatype reference introduces NO facts; it is a
/// sort marker only (see `Ty::Datatype`'s doc).
fn recursive_datatype_ref(name: &str) -> TrustTy {
    TrustTy::Datatype { name: name.to_string(), variants: Vec::new() }
}

// ─── RC-1: CANONICAL recursive-type lowering ────────────────────────────────
//
// THE DEFECT. Every `convert_ty` call starts with an EMPTY `adt_stack`, and the
// back-edge guards (`lower_adt_as_datatype`, `lower_enum_adt`, the struct arm)
// cut at the first re-entry of a type ALREADY ON THAT PATH. The cut point is
// therefore a property of the ROOT the type was reached from, not of the type.
// One rustc type reaches the dump as two different finite unrollings. Measured
// in `trust-clean/fixtures/structural-fold-corpus/xor_all.json`:
//
//     _1 : &Tree        →  Tree(full) → Arc(full) → …ArcInner.data = BY-NAME Tree
//     _6 : &Arc<Tree>   →  Arc(full)  → …ArcInner.data = Tree(full) → BY-NAME Arc
//
// so `(*_1 as Two).0`'s field type and `_6`'s declared type are the SAME rustc
// type at two different cut depths. `trust_clean::assignment_types::ty_eq` is
// strict structural equality, so `all_assignments_match` rejects the body and
// every lane gated on it (`prove::diagnose_fully_faithful_gate`, the fold
// recognizers) declines before it runs. The defect is in this producer; the
// consumer is right to be strict.
//
// THE CANONICAL RULE. Cut at a deterministic FEEDBACK VERTEX SET of the type's
// own reachability graph, exempting only the root of the current `convert_ty`
// call:
//
//   1. Discover the ADT reachability graph from the root: nodes are interned
//      `ty::Ty<'tcx>` (so `Vec<u8>` and `Vec<i32>` are DISTINCT nodes — the cut
//      set is never keyed on a generics-erased name), edges are field types
//      peeled through `&`/`*`/`[T]`/`[T; N]`/tuple/closure-upvar.
//   2. Compute its SCCs and the deterministic greedy feedback vertex set: while
//      a non-trivial SCC remains, delete its `canonical_cut_key`-least node.
//   3. Lower normally, but emit the by-name reference at every occurrence of a
//      cut-set member that is not this call's root.
//
// WHY THE RESULT IS UNIQUE (a function of the type alone). Two types in one SCC
// reach exactly the same node set (each reaches the other), so they discover the
// SAME graph and hence the same FVS. A type OUTSIDE that SCC discovers a subgraph
// that contains each SCC either wholly or not at all — and the greedy FVS is
// decided independently inside each SCC — so the FVS it computes is exactly the
// global FVS restricted to what it can reach. Therefore, for any type `C` reached
// below any root, the subtree emitted for `C` is byte-identical to the tree
// emitted for `C` as a root, UNLESS `C` is itself in the cut set. What changes
// is that the cut is now at a FIXED, canonically chosen type instead of wherever
// the root happened to enter the cycle.
//
// ─── RETRACTION: the surviving root dependence is NOT "irreducible" ──────────
//
// This paragraph used to end "The residual is irreducible: a finite
// representation of a cyclic type must cut each cycle at least once." The
// PREMISE is true; the CONCLUSION does not follow and the argument must not be
// repeated. Cutting somewhere constrains the REPRESENTATION. It does not force
// the representation to depend on the ROOT. Those are different claims.
//
// What actually survives here (residual R0 below) is that a cut point `C` is
// emitted as its FULL DEFINITION when it is the outermost nominal position of a
// `convert_ty` walk and as the bare by-name marker everywhere else. MEASURED, on
// the shipped `trust-clean/fixtures/structural-fold-corpus/xor_all.json`, for
// the single rustc type `Tree` — three distinct `Ty` values, at 4 / 24 / 3
// positions (byte counts below are `serde_json` compact bytes, 8079 / 29 / 693;
// the 8864 / 46 / 776 figures quoted elsewhere came from a pretty-printed dump):
//
//   `Adt{Tree, .., __v1_0: Adt{Arc, .. data: Datatype{Tree,[]}}}`  locals 1/5/9/11
//   `Datatype{Tree, []}`                                            24 nested slots
//   `Adt{Tree, .., __v1_0: Datatype{"std::sync::Arc",[]}}`          locals 4/6/7
//
// ─── PROVENANCE CORRECTION: those bytes are NOT R0's output ─────────────────
//
// The divergence above is real and the counts are right, but the ATTRIBUTION was
// wrong and had been repeated unchecked. Every shipped fold-corpus fixture
// PREDATES the canonical-cut rule:
//
//   structural-fold-corpus  regenerated 2026-07-24
//   level-fold-corpus       regenerated 2026-07-24
//   expr-fold-corpus        regenerated 2026-07-31
//   RC-1 (this rule) landed 2026-08-02  (`b398ea8875`)
//
// and `regenerate.sh`'s prebuilt `build/host/stage2/bin/trustc` is dated
// 2026-07-30 — also pre-RC-1. So no byte in this repo was produced by
// `canonical_cut_ref`, and the `structural_fold_corpus` 7-passed/2-failed and
// `level_fold_corpus` 8-passed/1-failed verdicts do not measure R0. CORROBORATED
// independently of the dates: across all 595 fixture JSONs, ZERO bare markers
// carry an INSTANTIATED def path (`<…>`) — and an instantiated path is
// `canonical_cut_ref`'s only output that no other producer can spell.
//
// What produced the three spellings is the LEGACY root-relative machinery, which
// this rule did not replace and which is still present below:
//   * root `&Tree`      → `Tree` pushed, reached again under `ArcInner.data`,
//                         `ctx.adt_stack.contains(&ty)` fires in `lower_enum_adt`
//                         → the 24 `Datatype{Tree,[]}` markers;
//   * root `&Arc<Tree>` → `Arc` pushed, `Tree` NOT on the stack so it EXPANDS,
//                         and its own `Arc` children hit the same guard
//                         → the third, 693-byte `Tree` spelling.
// Both are residuals R2/R3 (`adt_stack.contains` and the `cap_fields =
// !adt_stack.is_empty()` gates at the struct and enum arms), not R0. So the
// claim that `!ctx.adt_stack.is_empty()` in the `TyKind::Adt` arm is "the ENTIRE
// root special case" is FALSE: it is one of at least six root-relative decisions
// in this file, and it is not the one the shipped bytes exhibit. Anyone measuring
// R0 must first regenerate a corpus with a post-2026-08-02 `trustc`; there is no
// such binary in the tree, and building one is a full bootstrap.
//
// NOTE, for a reader trying to tell the producers apart in a dump: they cannot,
// for a non-generic type. `canonical_cut_ref` deliberately returns the EXACT
// erased def path when the type has no non-lifetime generic argument, so its
// marker for `Tree` is byte-identical to the legacy guard's and to
// `compact_oversized_field`'s. Only a generic cut point is distinguishable.
//
// The FIX THAT REMOVES IT ENTIRELY, so it is on record rather than rediscovered
// a fifth time: emit the marker for `C` at EVERY occurrence, the outermost one
// INCLUDED (i.e. delete the `!ctx.adt_stack.is_empty()` conjunct in the
// `TyKind::Adt` arm below — the ONLY place the cut rule special-cases the root),
// and carry the definitions OUT OF BAND in a type environment beside the body,
// `name -> definition`, each definition itself built with bare markers at cut
// points so the environment is finite and is a function of the type set alone.
// Then `rep` is a function of the type alone and syntactic equality on `Ty` IS
// type identity.
//
// ─── LANDED: the carrier was WIDENED and the producer FLIPPED, together ─────
//
// Both halves are now in the tree. History, because each step was a real block:
//
//   * The carrier `trust_types::VerifiableBody::datatype_defs` landed first,
//     back-filled at 1397 struct-literal sites across 226 files, with a
//     fail-closed keyed resolver.
//   * It landed with the WRONG VALUE TYPE, `BTreeMap<String, DatatypeVariants>`
//     — exactly `Ty::Datatype::variants`. A canonical cut point in this repo
//     does NOT lower to `Ty::Datatype`: `lower_adt_as_datatype` is def-path
//     gated to exactly `clean_kernel`'s `Level`/`Expr`/`ExprKind` (see
//     `is_level_path`'s `crate_name == "clean_kernel"` guard), so every other
//     recursive ADT — `Tree`, `TaggedTree`, and the `level::Level` the shipped
//     level-fold dumps actually contain — lowers through `lower_enum_adt` to a
//     `Ty::Adt`. Counted over all 2330 shipped fixture JSONs:
//
//         definitional `Ty::Adt`      (non-empty variants) : 7855
//         definitional `Ty::Datatype` (non-empty variants) :    0
//         bare markers                                     : 33758
//
//     so the narrow carrier could hold only the shape that occurs ZERO times.
//     Moving a cut point's definition into it DROPPED, with nowhere to put them:
//       - `VariantDef::discriminant` — the tag a `SwitchInt` compares against,
//         NOT reconstructible from the declaration index: 139 definitional ADTs
//         carry non-index discriminants (`std::cmp::Ordering` = [255,0,1] and
//         [-1,0,1]; this lane's own `tag_xor` = [10,20,30], which
//         `tests/structural_fold_corpus.rs` pins precisely to enforce "never
//         assume tag == declaration index"). Fabricating one would be a WRONG
//         fact, not a lossy one — `reflect.rs` mints kernel witnesses from it.
//       - the flat `__tag` / `__v{v}_{f}` view — all 7855 carry it, and
//         `legacy_flattened_variant_count` / `_fields` read it.
//       - `disc_index_safe` (319012 occurrences), `faithful_enum_repr` (5392),
//         `layout` (5297), `enum_layout` (4274), `adt_kind` (4274), `args` (615).
//         `enum_layout` gates the sound dense-tag
//         `Assume(min_disc <= d <= max_disc)`.
//     MEASURED, not predicted: rewriting each shipped fold-corpus body exactly
//     as a flip through the NARROW carrier would emit it and running the
//     production recognizer `sem_structural_fold_shape_of` on both gave
//     shipped 10-of-24 rows recognized, flipped 0-of-24 — every one failing at
//     `trustir_fold.rs`'s root-parameter destructure.
//   * So the value type was WIDENED to a full definitional `Ty`
//     (`BTreeMap<String, Ty>`), and the producer flipped in the SAME change so
//     the tree never sits half-converted. `Ty::Adt` definitions, discriminants
//     and all, now round-trip through the table untouched.
//
// The widening gave up the narrow value type's structural guarantee that an
// entry cannot disagree with its own key. That property is preserved by
// VALIDATION AT BOTH ENDS instead — `trust_types::insert_datatype_def` DERIVES
// the key from the value's own name (a caller cannot supply one), and
// `trust_types::datatype_definition` re-checks the agreement on every read, so
// even a deserialized table is inert where it disagrees. See `DatatypeDefs`.
//
// WHAT NO TEST HERE CAN SEE — unchanged, and it is why this file's change is
// argued rather than measured end to end. Every fold corpus is checked-in JSON
// produced by `build/host/stage2/bin/trustc`, dated 2026-07-30 — pre-RC-1 and
// pre-flip. `regenerate.sh` re-runs THAT prebuilt binary, so it reproduces
// pre-flip bytes; exercising a producer change needs a stage2 built from this
// crate, i.e. a full bootstrap. The flip's OBSERVABLE consequence is instead
// pinned on the real shipped bytes by
// `trust_clean::assignment_types::tests::
// r0_is_gone_on_the_shipped_bytes_one_rustc_type_now_yields_one_ty`, which
// rewrites `structural-fold-corpus/xor_all.json` exactly as this producer now
// emits it and runs the production consumer over the result.
//
// ─── REFUTED: "make the marker identity-bearing and no table is needed" ─────
//
// The tempting shortcut is that the carrier is only needed because the marker is
// ANONYMOUS: give a cut-point marker an identity that is (i) a function of the
// rustc type alone, (ii) instantiation-sensitive and (iii) distinguishable from
// the other two producers, and then the conjunct can go, equality is exact, and
// nothing ever has to resolve a marker back to its variants. It does not work,
// for two independent reasons, and both are now PINNED by tests rather than left
// as prose:
//
//   1. SOMETHING STILL NEEDS THE VARIANTS. `trust_clean::assignment_types::
//      place_type` types `Projection::Downcast(v)` by reading the base type's
//      variant list; a bare marker has none, so it declines. With the conjunct
//      deleted, `_1 : &Tree` is a marker and `_6 = &((*_1) as Two).0` — the very
//      statement R0 makes decline — becomes UNTYPEABLE. That trades a decline-
//      because-two-spellings-disagree for a decline-because-there-is-no-
//      structure-anywhere: it removes the capability instead of restoring it.
//      Pinned by `assignment_types::tests::
//      a_canonical_cut_marker_at_the_walk_root_cannot_type_a_downcast`.
//      The same reasoning applies to `modeled_enum_variant_count` (the enum
//      discriminant range fact), `datatype_functional`/`recursive_datatype_
//      functional`/`mutual_recursive_datatype_functional`/`threaded_budget_
//      functional` (all pattern-match `Ty::Datatype { variants, .. }` with a
//      non-empty list and go inert without one), and — most sharply —
//      `Sort::from_ty` → `trust_ir_contract::Sort::datatype_declarations`, which
//      SOURCES the `(declare-datatype …)` preamble text from the definitional
//      occurrence and documents that "a by-name reference contributes no
//      definition". Markers everywhere means the datatype is never declared while
//      `declare-fun … () <name>` still references its sort.
//
//   2. REQUIREMENT (iii) IS UNMET BY CONSTRUCTION. `canonical_cut_ref` returns
//      the erased def path for any type with no non-lifetime generic argument —
//      deliberately, so existing markers stay byte-identical. For exactly those
//      types its output is indistinguishable from the legacy `adt_stack`
//      back-edge guard's AND from `compact_oversized_field`'s. Making it
//      distinguishable needs a new `Ty` variant or field, i.e. a wire-form change
//      subject to the `stable_model_json` strip-list discipline and a pin re-
//      proof. Pinned by `assignment_types::tests::
//      cut_point_markers_stay_distinct_and_are_never_resolved_by_name`, which
//      also pins the fail-CLOSED half: every consumer declines on a bare marker
//      instead of binding it by name.
//
// ─── THE OPTION THAT NEEDED NO CARRIER, and what was landed instead ──────────
//
// A third shape was recorded here as the next thing to evaluate, because it
// deletes the root conjunct WITHOUT an out-of-band table. Define, for every X:
//
//   rep(X) = if X ∈ cut  then  Def1(X)  else  expand(X) with rep on its children
//   Def1(C) = C unrolled ONE level, with every cut-point occurrence in the
//             resulting fields replaced by the bare marker.
//
// A cut point then emits `Def1(C)` at EVERY position, root or not, so `rep` is a
// function of the type alone; markers appear only INSIDE a `Def1` body, so the
// tree is finite; and the variants are present at every occurrence, so consumer
// (1) above is satisfied in-band. What it costs is SIZE: every position that is
// a 29-byte marker becomes a full one-level definition. That is precisely the
// pressure `MAX_TYPE_LOWERING_PRODUCED_NODES` / `compact_oversized_field` exist
// to hold back (the 464 MB `Expr`/`ExprKind`/`Name` blow-up), and crossing that
// budget degrades a function to the fail-closed `Unsupported` marker — a
// capability loss traded for a canonicity gain.
//
// WHAT LANDED IS `Def1` WITH THE BODY DE-DUPLICATED. `cut_point_definition`
// computes exactly `Def1(C)` — that is what `expand_cut_point` means — but it is
// materialized ONCE per body, into `datatype_defs`, instead of at every one of
// `C`'s occurrences. So the canonicity argument above is inherited verbatim
// while the size objection disappears: each occurrence stays the 29-byte marker
// and the body carries one copy of the definition. The consumer pays a keyed
// table lookup where the in-band shape would have paid a tree copy.
//
// AND WHY THE CONSUMER CANNOT PATCH AROUND IT EITHER — BUILT, MEASURED,
// WITHDRAWN, so the next reader does not spend the same budget rediscovering it.
// The obvious consumer-side repair is to stop treating the by-name marker as an
// opaque leaf: harvest the definitional occurrences a body declares into a
// `name -> definition` environment and read `Ty` as the regular (equi-recursive)
// tree it denotes. That was implemented in `trust_clean::assignment_types` and
// it WORKS on the shipped bytes — `structural_fold_corpus` went 7 passed/2
// failed -> 9 passed/0 failed, and the raw defect inventory of the 124-row
// Expr-fold corpus fell from 105 failing assignments to 63. It was withdrawn
// anyway, for a reason that belongs here rather than there:
//
//   A `Ty::Datatype { name, variants: [] }` in a dump does NOT reliably mean
//   "a back-edge to an enclosing definition of `name`". `compact_oversized_field`
//   emits the very same shape for ANY oversized nested ADT field, with the
//   GENERICS-ERASED name, purely to bound the produced tree. So resolving such a
//   marker by NAME against a definition elsewhere in the body can bind a
//   compacted `Big<u8>` field to a declared `Big<i32>` — a FAIL-OPEN merge, and
//   an over-merging canonicalization is worse than the fail-closed decline it
//   replaces. Unanimity over the declared definitions of a name narrows this but
//   does not close it: it only fires when BOTH instantiations happen to appear
//   definitionally in the same body.
//
// Measured consequence of shipping it anyway, recorded because it is the gate
// that catches this: `prove::tests::authenticated_expr_fold_backrefs_repair_
// only_exact_manifested_bytes` fails. That test pins that a raw fixture carrying
// the back-reference defect must NOT type-check until its EXACT bytes are
// authenticated against a pinned digest, and that a one-byte drift revokes the
// repair. A body-wide name resolution admits the raw bytes with no
// authentication at all, which is a fail-closed authority boundary moving in the
// wrong direction.
//
// SO THE FIX IS THE PRODUCER'S, and it is the one now landed. The PREREQUISITE
// the withdrawal exposed — "every by-name marker must be IDENTITY-BEARING before
// any consumer may resolve one" — is met by a DIFFERENT mechanism than
// instantiating every marker's name, and the difference matters:
//
//   The consumer never resolves a marker BY SHAPE. It resolves a marker by
//   looking its name up in an EXPLICIT table that only `record_cut_definition`
//   writes. The legacy back-edge guard and `compact_oversized_field` write
//   nothing, so their markers have no entry and every consumer declines on them
//   exactly as before — no matter how their names are spelled. Identity is
//   supplied by WRITE AUTHORITY, not by the marker's text. See the block comment
//   on `record_cut_definition` for the three properties (write authority, key
//   space, fail-closed read validation) and for why a non-generic name shared
//   between a cut point and a compacted field denotes the same rustc type
//   anyway.
//
// WHY IT CANNOT MERGE TWO GENUINELY DIFFERENT TYPES. The only lossy element is
// the by-name marker. The first draft of this change named the marker with the
// GENERICS-ERASED def path (`recursive_datatype_ref(&safe_def_path_str(..))`,
// the same string the legacy back-edge guards use) and argued that this could
// not merge anything the status quo did not already merge. THAT ARGUMENT WAS
// WRONG, and the counterexample is exactly the one to worry about:
//
//     enum Foo<T> { Nil, Cons(T, Box<Foo<T>>) }
//     struct Pair { a: Foo<u8>, b: Foo<i32> }
//
// `Foo<u8>` and `Foo<i32>` are two DISTINCT interned types, each on its own
// cycle, so BOTH are cut points. Lowering `Pair`, each field is a non-root
// occurrence of a cut point, so with an erased marker BOTH fields emit
// `Datatype { name: "…::Foo", variants: [] }` and `Pair`'s two genuinely
// different fields compare EQUAL under `assignment_types::ty_eq`. The status quo
// does NOT do this: it expands each field one level (`__v1_0: u8` vs
// `__v1_1: i32`) before taking its back-edge, so the two stay distinguishable.
// That is a fail-OPEN regression — the original defect only made `ty_eq` decline
// (fail-closed), which is strictly the safer direction. An over-merging
// canonicalization is worse than the bug it fixes.
//
// So the marker emitted at a cut point is IDENTITY-BEARING: `canonical_cut_ref`
// names it with the CONCRETE instantiated path (`…::Foo<u8>` vs `…::Foo<i32>`)
// whenever the type has non-lifetime generic arguments, and with the plain
// erased path when it has none. A non-generic cut point (`Tree`, `Level`,
// `Expr`, `ExprKind` — every type the Lever A datatype lowering names) therefore
// keeps BYTE-IDENTICAL markers, so nothing that resolves a by-name datatype
// reference against a defining occurrence (`Sort::from_ty`'s
// `datatype_sort_from_ty`) changes at all; and a generic cut point gets one
// distinct sort name per instantiation, which is strictly MORE discriminating
// than both the status quo and the erased-marker draft.
//
// This is also why option (a) — "by-name for EVERY occurrence of a recursive
// ADT" — was rejected: even with instantiated names it would drop the structure
// of every nominal position, and the whole point of the root exemption is that
// the defining occurrence still carries the real variant list.
//
// FAIL-SAFE. Discovery is bounded by `MAX_CANONICAL_CUT_NODES`. If the bound is
// hit — the EXPANDING-generic recursion (`List<Box<List<T>>>`), whose node set is
// genuinely infinite and which `is_expanding_recursive_adt` deliberately leaves
// `Unsupported` — the cut set is EMPTY and lowering is byte-identical to today's.
// An empty cut set is also what a non-recursive type gets, so the overwhelming
// majority of types are untouched.
//
// KNOWN RESIDUALS (recorded, not hidden — none of them can merge two types, they
// can only cost canonicity, whose failure mode is a fail-closed `ty_eq` decline):
//
//   R0. RESOLVED — but it took TWO changes, and for three weeks only the first
//       had landed. It was: a cut point is its full definition at the outermost
//       nominal position of a walk and a bare marker everywhere else, so one
//       rustc type reaches the dump as several unequal `Ty` values. The marker
//       is now emitted at EVERY occurrence, the root included, and the
//       definition lives out of band in `VerifiableBody::datatype_defs` — see
//       the LANDED section above.
//
//       THE SECOND CHANGE, and why the first alone did nothing: all of the
//       above is reached only when `ty` is IN the cut set, and the cut set was
//       always EMPTY on real code. `nominal_frontier` had no `TyKind::Pat` arm
//       (it fell through a `_ => {}`), and `NonNull`'s single field IS a pattern
//       type — `pattern_type!(*const T is !null)` — so discovery could not get
//       from `Arc`/`Box` to the pointee, no `Arc`/`Box`-recursive user type ever
//       reached itself, and every such cycle was cut by the LEGACY root-relative
//       `adt_stack` guard instead. Exactly R2's failure mode, one constructor
//       over. Measured before the fix, across all 441 shipped trust-clean
//       fixtures: zero `datatype_defs` entries and zero cut markers, while
//       `xor_all.json` alone carried `SOURCE::Tree` as 7 full `Ty::Adt`s AND 24
//       bare markers — R0 itself, in bytes, under a commit claiming it gone.
//       The lesson is recorded in R7.
//
//       `nominal_frontier` is now EXHAUSTIVE over `TyKind` with no `_` arm, so
//       the next constructor upstream adds cannot silently re-open this.
//       `trust_clean::assignment_types::tests::r0_is_gone_on_the_shipped_bytes_
//       one_rustc_type_now_yields_one_ty` pins the CONSUMER half; note its SCOPE
//       block — it flips the body itself, so it never could have caught this.
//   R7. NEW, and it is a lesson rather than a residual: a discovery walk that
//       silently under-approximates does not fail, it DEGRADES — quietly, into
//       the legacy path, with every test still green. R1 and R2 are the two
//       remaining ways to land in that fallback and both are recorded as
//       fail-closed; what R0's second half showed is that "fail-closed" hides
//       the fallback so well that a headline property can be reported resolved
//       while it is measurably live on disk. Any future claim that a lowering
//       property holds must be measured on FRESHLY REGENERATED bytes from a
//       stage2 carrying the change — not on a fixture, and not on a body the
//       test itself constructed.
//   R1. The budget fallback is root-relative: a root whose graph exceeds
//       `MAX_CANONICAL_CUT_NODES` gets an EMPTY cut set and therefore the legacy
//       root-relative lowering, while a smaller root reaching the same cycle
//       still cuts canonically. UNCHANGED, and it is one of the two cases where
//       the retained `adt_stack.contains` termination fail-safes can still fire.
//   R2. `nominal_frontier` does not peel `TyKind::Alias`, but `convert_ty_in_env`
//       DOES normalize opaque aliases before descending. A cycle that closes only
//       through an alias is invisible to discovery, so it is cut by the legacy
//       `adt_stack` guard instead. UNCHANGED, and the second of those two cases.
//   R3. RESOLVED. It was: the `cap_fields` compaction gates in the struct arm and
//       `lower_enum_adt` are keyed on `!adt_stack.is_empty()`, i.e. root-relative.
//       Both are now UNCONDITIONAL, so a field slot is a function of the field
//       type alone. See R5 for what that leaves.
//   R4. `canonical_cut_key` is total only up to the injectivity of
//       `(def-path depth, instantiated path, CrateNum, DefIndex)`. Two distinct
//       interned `Ty` sharing all four would tie, and the tie is then broken by
//       discovery order, which is root-relative. MIR types reach this code with
//       erased regions, so lifetimes cannot produce such a pair; it would take a
//       printer collision between two different concrete argument lists on one
//       `DefId`. UNCHANGED.
//   R5. NEW, and it is R3's remainder rather than a regression: compaction is a
//       decision the PARENT makes about a field, so a type whose own lowering
//       exceeds `MAX_DATATYPE_FIELD_NODES` is a bare marker as a field and its
//       full self as a local. That is POSITION-relative, not root-relative — the
//       decision is a function of `(field type)` alone and no longer of how the
//       walk arrived — and it is fail-CLOSED, because a compacted marker has no
//       table entry and every consumer declines on it. It is also far rarer than
//       the gate it replaced: under markers-everywhere each recursive tower is
//       already a one-node marker before the 64-node cap can see it (measured on
//       the shipped corpus, `Arc<Tree>` = 15 nodes).
//   R6. NEW, and inherent to any resource guard: `MAX_TYPE_LOWERING_PRODUCED_
//       NODES` and `MAX_CUT_DEFINITION_NESTING` are cumulative counters, so a
//       type lowered after the budget is spent degrades where the same type
//       lowered earlier would not. The cut MARKER itself is exempt (it is
//       emitted before every budget bail, see `convert_ty_inner`), so this can
//       only cost a DEFINITION, never split one type into two markers. A missing
//       definition is the pre-carrier decline.

/// Node bound for the canonical-cut discovery walk. Reaching it yields an EMPTY
/// cut set (i.e. exactly today's root-relative lowering) — never a partial cut
/// set, which would not be canonical.
const MAX_CANONICAL_CUT_NODES: usize = MAX_TYPE_LOWERING_NODES;

/// The ordering key the greedy feedback vertex set picks its cut points with.
/// EVERY component must be a function of the TYPE ALONE — anything derived from
/// the walk (discovery index, insertion order, the root) would make the cut set
/// root-relative again, which is the very defect RC-1 exists to remove.
type CanonicalCutKey = (usize, String, u32, u32);

/// The deterministic total order the greedy feedback vertex set picks its cut
/// points with: the SHALLOWEST def path in the cycle first (so a cycle through
/// `Tree`/`std::sync::Arc`/`std::ptr::NonNull`/`alloc::sync::ArcInner` is cut at
/// `Tree`, the type the cycle is ABOUT, not at an `std` container internal),
/// then the fully-instantiated path, then the type's `DefId` (`CrateNum`,
/// `DefIndex`) so two distinct types that happen to PRINT the same still order
/// deterministically rather than falling back on discovery order. See residual
/// R4 on the block comment above for what is left.
fn canonical_cut_key<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> CanonicalCutKey {
    let TyKind::Adt(def, args) = ty.kind() else {
        return (usize::MAX, String::new(), u32::MAX, u32::MAX);
    };
    let did = def.did();
    // Same renderer as `canonical_cut_ref` / the `TyKind::Adt` arm, so the cut
    // ordering key cannot disagree with the name the cut is emitted under.
    let erased = crate::sysroot_authenticated_def_path_str(tcx, did);
    let segments = erased.matches("::").count();
    (
        segments,
        crate::sysroot_authenticated_def_path_str_with_args(tcx, did, *args),
        did.krate.as_u32(),
        did.index.as_u32(),
    )
}

/// The by-name reference a CUT POINT lowers to.
///
/// IDENTITY-BEARING, and that is the whole point (see "WHY IT CANNOT MERGE TWO
/// GENUINELY DIFFERENT TYPES" above): a cut point is emitted with no structure at
/// all, so its name is the ONLY thing distinguishing it from another instantiation
/// of the same generic ADT. `Foo<u8>` and `Foo<i32>` are two distinct cut points
/// and must not collapse to one marker.
///
/// A type with no non-lifetime generic arguments keeps the EXACT erased def path
/// the legacy back-edge guards emit (`recursive_datatype_ref(&safe_def_path_str)`),
/// so every marker in the Lever A `Level`/`Expr`/`ExprKind` cluster — and `Tree`
/// in the structural-fold corpus — is byte-identical to today's. Only a generic
/// cut point gains the `<args>` suffix, and there the alternative is a merge.
fn canonical_cut_ref<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> TrustTy {
    let TyKind::Adt(def, args) = ty.kind() else {
        // Unreachable: `nominal_frontier` only ever admits `TyKind::Adt` nodes,
        // so only an ADT can be in the cut set. Fail closed rather than invent a
        // name if that ever stops holding.
        return unsupported_ty("TyKind", "canonical cut point was not a nominal ADT");
    };
    let did = def.did();
    let erased = crate::sysroot_authenticated_def_path_str(tcx, did);
    let has_non_lifetime_args = args.types().next().is_some() || args.consts().next().is_some();
    if has_non_lifetime_args {
        recursive_datatype_ref(&crate::sysroot_authenticated_def_path_str_with_args(
            tcx, did, *args,
        ))
    } else {
        recursive_datatype_ref(&erased)
    }
}

// ─── R0 REMOVED: the out-of-band definition table, and who may write it ──────
//
// A cut point is now the by-name marker at EVERY occurrence, the walk ROOT
// INCLUDED, and its definition lives in `trust_types::VerifiableBody::
// datatype_defs` — keyed by exactly the name `canonical_cut_ref` mints. So
// `rep` is a function of the TYPE alone and syntactic equality on `Ty` IS type
// identity for a cut point.
//
// THE TABLE IS WRITTEN HERE AND NOWHERE ELSE. That is the whole mechanism that
// keeps a cut point apart from `compact_oversized_field`, which emits the
// IDENTICAL `Ty::Datatype { name, variants: [] }` shape and must NEVER be
// resolvable — it is a SIZE BOUND, not a back-edge, and binding a compacted
// `Big<u8>` field to a declared `Big<i32>` is the fail-OPEN the withdrawn
// consumer-side by-name search was rejected for. Three properties keep them
// apart, and none of them is "look at the shape of the marker":
//
//   1. WRITE AUTHORITY. `record_cut_definition` is the sole writer, and it is
//      reached from exactly one place: the cut-point arm at the top of
//      `convert_ty_inner`. `compact_oversized_field` writes nothing, ever, so a
//      compacted marker has no entry and every consumer declines on it exactly
//      as it did before this table existed.
//   2. KEY SPACE. The key is `canonical_cut_ref`'s name — the INSTANTIATED def
//      path for a type with non-lifetime generic arguments. `compact_oversized_
//      field` names with the ERASED path of the already-lowered `Ty`, so for the
//      generic case the two name spaces are disjoint by construction
//      (`k::Big<u8>` vs `k::Big`). For the NON-generic case the two names
//      coincide — and there they denote the SAME rustc type, because a
//      non-generic cut point reached at a field position is emitted as a
//      one-node marker by rule 1 long before the 64-node compaction cap can see
//      it, so compaction never observes a cut point at all. Resolving such a
//      name is therefore correct, not a merge.
//   3. FAIL-CLOSED READ. `trust_types::datatype_definition` re-validates that an
//      entry names itself before serving it, so even a hand-built or
//      deserialized table cannot make a marker mean something else.

/// Nesting bound for cut-point definition recording. Each cut point's definition
/// is built at most once per body, and building it can reach ANOTHER cut point,
/// which builds its definition in turn. The chain is bounded by the size of the
/// cut set, but that is only bounded by `MAX_CANONICAL_CUT_NODES`; cap the
/// nesting so a pathological type graph cannot exhaust the extraction stack.
/// Crossing it REFUSES the definition (the marker then resolves to nothing and
/// every consumer declines) — fail-closed, never a fabricated definition.
const MAX_CUT_DEFINITION_NESTING: usize = 64;

/// Body-scoped accumulator for the out-of-band datatype definition table.
#[derive(Default)]
struct DatatypeDefCollector {
    /// The definitions recorded so far, keyed by `canonical_cut_ref`'s name.
    defs: trust_types::DatatypeDefs,
    /// Names whose definition is being built right now. This is what makes a
    /// SELF-recursive cut point terminate: `Tree`'s definition reaches `Tree`,
    /// which finds its own name in progress and emits the marker without
    /// recursing.
    in_progress: std::collections::BTreeSet<String>,
    /// Names permanently refused for this body — a malformed definition, a
    /// second DIFFERENT definition of one name, or a nesting-bound overrun. A
    /// refused name is never retried, so one body can never serve two
    /// disagreeing definitions of one name.
    refused: std::collections::BTreeSet<String>,
}

thread_local! {
    static DATATYPE_DEFS: std::cell::RefCell<DatatypeDefCollector> =
        std::cell::RefCell::new(DatatypeDefCollector::default());
}

/// RAII scope for ONE function's definition table.
///
/// Clears the accumulator on entry and on drop, so a table can never inherit an
/// entry from the previously extracted function — an entry is an assertion about
/// THIS body's markers and nothing else. Thread-local, like `FAITHFUL_SCALARS`
/// above, because rustc runs `mir_built` in parallel and each worker thread owns
/// its own extraction.
pub(crate) struct DatatypeDefScope(());

impl DatatypeDefScope {
    pub(crate) fn begin() -> Self {
        DATATYPE_DEFS.with(|c| *c.borrow_mut() = DatatypeDefCollector::default());
        DatatypeDefScope(())
    }
}

impl Drop for DatatypeDefScope {
    fn drop(&mut self) {
        DATATYPE_DEFS.with(|c| *c.borrow_mut() = DatatypeDefCollector::default());
    }
}

/// The definitions recorded so far in the current [`DatatypeDefScope`].
pub(crate) fn collected_datatype_defs() -> trust_types::DatatypeDefs {
    DATATYPE_DEFS.with(|c| c.borrow().defs.clone())
}

/// The full definitional `Ty` a cut point stands for: `ty` expanded EXACTLY ONE
/// level, with every cut-point occurrence inside it — `ty` itself included —
/// left as the by-name marker.
///
/// AS-IF-ROOT, and that is the point. The sub-context is FRESH: depth 0, full
/// node/produced budgets, empty `adt_stack`, empty memo. A definition built with
/// the enclosing walk's leftover budget would depend on how deep the walk was
/// when it first reached the cut point, which is the root dependence this whole
/// change removes — merely relocated into the table.
///
/// The cut set is REUSED rather than recomputed. `greedy_fvs_is_root_independent`
/// pins that for any successor-closed subset `S`, `cut(S) == cut(U) ∩ S`; the set
/// reachable from `ty` is successor-closed inside the set reachable from the
/// enclosing root, so `canonical_cut_set(tcx, ty)` and `ctx.canonical_cut`
/// restricted to it agree — reusing is the same answer for one discovery walk
/// instead of two.
fn cut_point_definition<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    marker_name: &str,
    ctx: &TyLoweringCtx<'tcx>,
) -> TrustTy {
    let mut sub = TyLoweringCtx {
        typing_env: ctx.typing_env,
        canonical_cut: ctx.canonical_cut.clone(),
        // Expand THIS occurrence, once. Every other cut point below it — and
        // every FURTHER occurrence of this one — still takes the marker arm.
        expand_cut_point: Some(ty),
        ..TyLoweringCtx::default()
    };
    rename_definition(convert_ty_inner(tcx, ty, &mut sub), marker_name)
}

/// Restate a definition's own name as the KEY it will be filed under.
///
/// `lower_enum_adt` / `lower_adt_as_datatype` name a definition with the
/// GENERICS-ERASED def path, while `canonical_cut_ref` keys a generic cut point
/// by its INSTANTIATED path. Without this restatement `Foo<u8>`'s definition
/// would be filed under `k::Foo<u8>` while naming itself `k::Foo`, and
/// `trust_types::datatype_definition`'s key/value agreement check would refuse
/// to serve it. For a NON-generic cut point the two spellings are already
/// identical and this is the identity.
fn rename_definition(mut def: TrustTy, name: &str) -> TrustTy {
    match &mut def {
        TrustTy::Adt { name: n, .. } | TrustTy::Datatype { name: n, .. } => {
            if n != name {
                *n = name.to_string();
            }
        }
        _ => {}
    }
    def
}

/// Record `ty`'s definition under `marker_name`, at most once per body.
///
/// FAIL-CLOSED at every step: an already-refused name, an over-deep nesting
/// chain, a definition that carries no structure, and a SECOND definition that
/// disagrees with one already recorded all leave the name UNDEFINED, and an
/// undefined marker is exactly the pre-table decline.
fn record_cut_definition<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    marker_name: &str,
    ctx: &TyLoweringCtx<'tcx>,
) {
    let reserved = DATATYPE_DEFS.with(|c| {
        let mut c = c.borrow_mut();
        if c.defs.contains_key(marker_name)
            || c.in_progress.contains(marker_name)
            || c.refused.contains(marker_name)
        {
            return false;
        }
        if c.in_progress.len() >= MAX_CUT_DEFINITION_NESTING {
            c.refused.insert(marker_name.to_string());
            return false;
        }
        c.in_progress.insert(marker_name.to_string());
        true
    });
    if !reserved {
        return;
    }

    let def = cut_point_definition(tcx, ty, marker_name, ctx);

    DATATYPE_DEFS.with(|c| {
        let mut c = c.borrow_mut();
        c.in_progress.remove(marker_name);
        // `insert_datatype_def` derives the key from the value's OWN name, so a
        // definition can never be filed under a name it does not claim; it
        // returns false for a value with no name, a value with no structure, and
        // a conflicting redefinition (which it also removes).
        if !trust_types::insert_datatype_def(&mut c.defs, def) {
            c.defs.remove(marker_name);
            c.refused.insert(marker_name.to_string());
        }
    });
}

/// Collect the FIRST nominal ADT on every path below `ty`, peeling exactly the
/// type constructors the lowering itself descends through. This is the edge
/// relation of the reachability graph; it is a SUPERSET of the relation the
/// datatype lowering uses (`datatype_child_field_ty` cuts at every nominal child
/// unconditionally), so a feedback vertex set computed here breaks every cycle
/// the lowering can actually walk.
fn nominal_frontier<'tcx>(
    ty: ty::Ty<'tcx>,
    depth: usize,
    out: &mut Vec<ty::Ty<'tcx>>,
) {
    if depth >= MAX_TYPE_LOWERING_DEPTH {
        return;
    }
    match ty.kind() {
        TyKind::Adt(..) => out.push(ty),
        TyKind::Ref(_, inner, _) => nominal_frontier(*inner, depth + 1, out),
        TyKind::RawPtr(pointee, _) => nominal_frontier(*pointee, depth + 1, out),
        TyKind::Slice(elem) => nominal_frontier(*elem, depth + 1, out),
        TyKind::Array(elem, _) => nominal_frontier(*elem, depth + 1, out),
        TyKind::Tuple(fields) => {
            for field in fields.iter() {
                nominal_frontier(field, depth + 1, out);
            }
        }
        TyKind::Closure(_, args) => {
            for upvar in args.as_closure().upvar_tys().iter() {
                nominal_frontier(upvar, depth + 1, out);
            }
        }
        TyKind::Coroutine(_, args) => {
            for upvar in args.as_coroutine().upvar_tys().iter() {
                nominal_frontier(upvar, depth + 1, out);
            }
        }
        // Trust: a pattern type is a restricted-value SUBSET of its base, and
        // `convert_ty_inner` lowers it as that base (`TyKind::Pat` arm) — so a
        // cycle through one is a cycle the lowering really walks. Omitting this
        // arm made `NonNull` opaque to cycle discovery, and `NonNull`'s field is
        // `pattern_type!(*const T is !null)`: every `Arc`/`Box`-recursive user
        // type reaches itself only through it. The feedback vertex set therefore
        // came back EMPTY for `enum Tree { Node(Arc<Tree>) }`, the canonical-cut
        // lowering never fired on a single real dump, and recursion fell back to
        // the `adt_stack` cut — which is root-relative, i.e. R0.
        TyKind::Pat(inner, _) => nominal_frontier(*inner, depth + 1, out),
        // Trust: EXHAUSTIVE ON PURPOSE — no `_` arm. This function's contract
        // (above) is that it peels exactly what the lowering peels, and a silent
        // fallthrough is how that contract was broken: the two walks drifted and
        // nothing failed loudly, it just quietly stopped finding cycles. Every
        // variant below is here because the lowering CANNOT walk a modeled cycle
        // through it — it either lowers opaquely (`Dynamic`, `FnPtr`, `FnDef`,
        // `CoroutineWitness`, whose upvars lower empty), lowers to
        // `unsupported_ty` (`Foreign`, `CoroutineClosure`, `UnsafeBinder`), or
        // has no nominal content at all. When an upstream merge adds a `TyKind`,
        // this match stops compiling and someone has to make that judgement
        // deliberately instead of inheriting a fallthrough.
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Foreign(_)
        | TyKind::Str
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..)
        | TyKind::UnsafeBinder(_)
        | TyKind::Dynamic(..)
        | TyKind::CoroutineClosure(..)
        | TyKind::CoroutineWitness(..)
        | TyKind::Never
        | TyKind::Alias(..)
        | TyKind::Param(_)
        | TyKind::Bound(..)
        | TyKind::Placeholder(_)
        | TyKind::Infer(_)
        | TyKind::Error(_) => {}
    }
}

/// The nominal ADTs directly reachable from `ty`'s own fields (every variant of
/// an enum, `all_fields` of a struct/union).
fn adt_field_successors<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Vec<ty::Ty<'tcx>> {
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for variant in adt_def.variants().iter() {
        for field in variant.fields.iter() {
            nominal_frontier(field.ty(tcx, *args).skip_normalization(), 0, &mut out);
        }
    }
    out
}

/// The canonical feedback vertex set of the ADT reachability graph rooted at
/// `root`. Empty when the graph is acyclic or when discovery hit its bound.
fn canonical_cut_set<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Ty<'tcx>,
) -> trust_types::fx::FxHashSet<ty::Ty<'tcx>> {
    // ── discovery (bounded) ────────────────────────────────────────────────
    let mut order: Vec<ty::Ty<'tcx>> = Vec::new();
    let mut index: FxHashMap<ty::Ty<'tcx>, usize> = FxHashMap::default();
    let mut seeds = Vec::new();
    nominal_frontier(root, 0, &mut seeds);
    for seed in seeds {
        if index.insert(seed, order.len()).is_none() {
            order.push(seed);
        }
    }
    let mut edges: Vec<Vec<usize>> = Vec::new();
    let mut head = 0usize;
    while head < order.len() {
        if order.len() > MAX_CANONICAL_CUT_NODES {
            return trust_types::fx::FxHashSet::default();
        }
        let node = order[head];
        let mut succ = Vec::new();
        for child in adt_field_successors(tcx, node) {
            let id = match index.get(&child) {
                Some(id) => *id,
                None => {
                    if order.len() > MAX_CANONICAL_CUT_NODES {
                        return trust_types::fx::FxHashSet::default();
                    }
                    let id = order.len();
                    index.insert(child, id);
                    order.push(child);
                    id
                }
            };
            if !succ.contains(&id) {
                succ.push(id);
            }
        }
        edges.push(succ);
        head += 1;
    }
    debug_assert_eq!(edges.len(), order.len());

    // ── deterministic greedy feedback vertex set ───────────────────────────
    // Keys are computed LAZILY. `canonical_cut_key` renders two rustc def paths
    // per node, and `canonical_cut_set` runs once per `convert_ty` call — i.e.
    // once per local, per place, per body. The overwhelmingly common graph is
    // ACYCLIC, and an acyclic graph needs no key at all: the first SCC pass finds
    // no non-trivial component and the loop exits before any key is rendered.
    let mut keys: Vec<Option<CanonicalCutKey>> = vec![None; order.len()];
    let mut cut: trust_types::fx::FxHashSet<ty::Ty<'tcx>> = trust_types::fx::FxHashSet::default();
    for pick in greedy_feedback_vertex_set(&edges, &mut |node| {
        keys[node].get_or_insert_with(|| canonical_cut_key(tcx, order[node])).clone()
    }) {
        cut.insert(order[pick]);
    }
    cut
}

/// The deterministic greedy feedback vertex set of `edges`: while a non-trivial
/// strongly connected component remains, delete its `key_of`-least node.
///
/// Split out from `canonical_cut_set` — and taking no `TyCtxt` — because THIS is
/// the function root-independence rests on, and it is the part that can be tested
/// without a compiler session. The property it must have (see
/// `greedy_fvs_is_root_independent`) is:
///
///   for every successor-closed subset `S` of the nodes, and every re-indexing of
///   `S`, the cut computed on the induced subgraph equals the global cut ∩ `S`.
///
/// It holds because (i) a successor-closed subset contains each SCC wholly or not
/// at all, (ii) a path leaving an SCC never returns, so an SCC's internal SCC
/// structure after deletions depends only on its own induced subgraph, and (iii)
/// the pick is by `key_of` alone, never by node index or iteration order. Point
/// (iii) is why `key_of` must be a function of the underlying type only.
fn greedy_feedback_vertex_set(
    edges: &[Vec<usize>],
    key_of: &mut dyn FnMut(usize) -> CanonicalCutKey,
) -> Vec<usize> {
    let mut alive: Vec<bool> = vec![true; edges.len()];
    let mut cut: Vec<usize> = Vec::new();
    loop {
        let components = strongly_connected_components(edges, &alive);
        let mut progressed = false;
        for component in components {
            let self_loop = component.len() == 1 && edges[component[0]].contains(&component[0]);
            if component.len() < 2 && !self_loop {
                continue;
            }
            let mut best: Option<(usize, CanonicalCutKey)> = None;
            for node in component.iter().copied() {
                let key = key_of(node);
                let better = match &best {
                    None => true,
                    Some((_, best_key)) => key < *best_key,
                };
                if better {
                    best = Some((node, key));
                }
            }
            let Some((pick, _)) = best else { continue };
            alive[pick] = false;
            cut.push(pick);
            progressed = true;
        }
        if !progressed {
            break;
        }
    }
    cut
}

/// Tarjan SCCs of the subgraph induced on the `alive` nodes. Iterative, so a
/// deep type graph cannot overflow the extraction stack.
fn strongly_connected_components(edges: &[Vec<usize>], alive: &[bool]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut counter = 0usize;
    for start in 0..n {
        if !alive[start] || index[start] != usize::MAX {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some((node, next)) = work.pop() {
            if next == 0 {
                index[node] = counter;
                low[node] = counter;
                counter += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            let mut descended = false;
            let successors = &edges[node];
            for cursor in next..successors.len() {
                let child = successors[cursor];
                if !alive[child] {
                    continue;
                }
                if index[child] == usize::MAX {
                    work.push((node, cursor + 1));
                    work.push((child, 0));
                    descended = true;
                    break;
                } else if on_stack[child] {
                    low[node] = low[node].min(index[child]);
                }
            }
            if descended {
                continue;
            }
            if low[node] == index[node] {
                let mut component = Vec::new();
                while let Some(top) = stack.pop() {
                    on_stack[top] = false;
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                out.push(component);
            }
            if let Some((parent, _)) = work.last().copied() {
                low[parent] = low[parent].min(low[node]);
            }
        }
    }
    out
}

/// Maximum node count for a SINGLE flattened variant/struct-field subtree before
/// it is compacted (verifier-perf, Lever A). Small recursive enums and ordinary
/// scalar/pointer payloads stay well under it; the Arc/Atomic/UnsafeCell-laden
/// kernel `Expr`/`Level` pointer fields (the source of the thousands-of-nodes
/// blow-up that OOM-killed extraction / stalled `place_ty`) exceed it and
/// collapse to a by-name datatype reference, which keeps the enclosing type
/// MODELED (not bailed to `Unsupported`) so the Lever-A win lands.
const MAX_DATATYPE_FIELD_NODES: usize = 64;

/// Compact an oversized recursive-enum/struct field subtree to a small, modeled
/// placeholder. If the subtree is an aggregate carrying a name (an `Adt` or a
/// `Datatype`), preserve that name as a by-name `Ty::Datatype` reference (so the
/// sort stays a stable per-type datatype sort). A pointer/ref keeps its pointer
/// shape (its SMT sort is an integer address) and compacts the pointee. Otherwise
/// fall back to a generic opaque datatype reference. SOUNDNESS: the result is
/// always a MODELED, fact-free sort — never `Unsupported` (which would fail
/// closed) and never a fabricated constraint. An over-large field is a
/// pointer-wrapped aggregate whose SMT value is an opaque address/datatype const
/// anyway, so collapsing it loses no SOUND obligation (the scalar leaves that
/// matter — the `__tag` discriminant and small payloads — are under the cap and
/// keep full detail).
fn compact_oversized_field(ty: &TrustTy) -> TrustTy {
    match ty {
        TrustTy::Adt { name, .. } | TrustTy::Datatype { name, .. } => recursive_datatype_ref(name),
        TrustTy::Ref { mutable, inner } => {
            TrustTy::Ref { mutable: *mutable, inner: Box::new(compact_oversized_field(inner)) }
        }
        TrustTy::RawPtr { mutable, pointee } => TrustTy::RawPtr {
            mutable: *mutable,
            pointee: Box::new(compact_oversized_field(pointee)),
        },
        _ => recursive_datatype_ref("__trust_compacted_aggregate"),
    }
}

/// Count nodes in a lowered `Ty`, short-circuiting once `cap` is reached (so a
/// huge tree costs O(cap), not O(size)). Used only to decide the size-collapse in
/// `lower_enum_adt` / the recursive struct lowering.
fn ty_node_count(ty: &TrustTy, cap: usize) -> usize {
    fn go(ty: &TrustTy, cap: usize, acc: &mut usize) {
        if *acc >= cap {
            return;
        }
        *acc += 1;
        match ty {
            TrustTy::Ref { inner, .. } => go(inner, cap, acc),
            TrustTy::RawPtr { pointee, .. } => go(pointee, cap, acc),
            TrustTy::Slice { elem }
            | TrustTy::Array { elem, .. }
            | TrustTy::SymArray { elem, .. } => go(elem, cap, acc),
            TrustTy::Tuple(tys) => {
                for t in tys {
                    go(t, cap, acc);
                }
            }
            // A platform-internal std type can have a very large implementation tree.
            // Count it as ONE node (the `*acc += 1` at the top of `go`) and do NOT
            // descend, so a lock-bearing user aggregate (`Mutex<T>` inside a struct such
            // as `sink::Shared`) stays UNDER the field-compaction cap and remains fully
            // EXPANDED for the drop-glue walk — otherwise the aggregate collapses to an
            // opaque `Ty::Datatype` the classifier must decline. This is precision only:
            // the bridge now grants Drop authority to two exact pthread leaf paths and
            // fails closed on every other `std::sys` type. Undercounting only REDUCES
            // compaction (strictly more precision, never a fabricated fact); scoped to
            // `std::sys::` so the kernel `Expr`/`Level` pointer towers that motivated the
            // cap are untouched.
            TrustTy::Adt { name, .. } if name.starts_with("std::sys::") => {}
            TrustTy::Adt { fields, variants, .. } => {
                for (_, t) in fields {
                    go(t, cap, acc);
                }
                for v in variants {
                    for (_, t) in &v.fields {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Datatype { variants, .. } => {
                for (_, fs) in variants {
                    for (_, t) in fs {
                        go(t, cap, acc);
                    }
                }
            }
            TrustTy::Closure { upvars, .. } | TrustTy::Coroutine { upvars, .. } => {
                for t in upvars {
                    go(t, cap, acc);
                }
            }
            _ => {}
        }
    }
    let mut acc = 0;
    go(ty, cap, &mut acc);
    acc
}

struct TyLoweringCtx<'tcx> {
    depth: usize,
    remaining_nodes: usize,
    /// verifier-perf: cumulative count of PRODUCED `TrustTy` nodes materialized
    /// across THIS function's type lowering (fresh trees + cache-hit clones).
    /// Once it crosses `produced_budget`, lowering degrades to the fail-closed
    /// recursive-ADT marker. See `MAX_TYPE_LOWERING_PRODUCED_NODES`.
    produced_nodes: usize,
    /// Per-walk cached produced-node budget (read once at construction, so an env
    /// override is honored without re-parsing per node). `usize::MAX` disables.
    produced_budget: usize,
    /// The nominal ADTs currently being expanded on this path. Read ONLY by the
    /// termination fail-safes (`adt_stack.contains`) and the expanding-generic
    /// guard; it no longer gates any REPRESENTATION choice — see residual R1/R2
    /// on the block comment above for the two cases where those fail-safes can
    /// still fire, and why they cannot be removed.
    adt_stack: Vec<ty::Ty<'tcx>>,
    /// RC-1 (canonical recursive-type lowering): the deterministic feedback
    /// vertex set of THIS walk's type-reachability graph. EVERY occurrence of a
    /// member — the walk's root included — lowers to the by-name reference, so
    /// one rustc type has exactly one representation regardless of which root it
    /// was reached from and of where in the walk it appears. Empty for an
    /// acyclic type and whenever discovery hit its bound — in both cases
    /// lowering is byte-identical to the pre-RC-1 behavior. See the block
    /// comment on `canonical_cut_set`.
    canonical_cut: trust_types::fx::FxHashSet<ty::Ty<'tcx>>,
    /// The ONE cut-point occurrence that expands instead of taking the marker
    /// arm, set only by `cut_point_definition` while it builds that type's
    /// out-of-band definition. `None` in every ordinary walk.
    ///
    /// NOT a root exemption: it names a specific type, is cleared the moment it
    /// fires, and lives in a throwaway sub-context whose result goes to the
    /// definition table rather than into the surrounding tree.
    expand_cut_point: Option<ty::Ty<'tcx>>,
    /// verifier-coverage: the `TypingEnv` in which alias
    /// normalization is attempted. `None` means "do not normalize
    /// aliases" — every non-`Free` alias stays `Unsupported` (the legacy
    /// behavior, preserved for the many `convert_ty` call sites that do
    /// not have a body's env in scope). `Some(env)` additionally enables
    /// the *narrow*, build-safe `AliasTyKind::Opaque` reveal documented on
    /// the `TyKind::Alias` arm. (`Free` aliases are expanded structurally
    /// regardless — they do not drive the trait solver.)
    typing_env: Option<ty::TypingEnv<'tcx>>,
    /// verifier-perf: memoization cache for already-lowered
    /// types in this walk. Stage2-rustc internals like `GlobalCtxt`
    /// reach the same nested `Arena<…>` / `Vec<…>` subtypes many times
    /// across the per-function MIR walk; without a cache, each visit
    /// repeats the entire subtree walk and decrements the node budget
    /// for each repeat — which is what caused the previous "node budget
    /// exceeded 4096" reports in otherwise-lowerable functions. The
    /// cache is per-`convert_ty` call (resets between functions), so it
    /// doesn't leak across compilations or carry state between MIR
    /// bodies. Keyed by the raw `Ty` pointer (rustc interns types, so
    /// equality is pointer-identity).
    cache: FxHashMap<ty::Ty<'tcx>, TrustTy>,
}

impl<'tcx> Default for TyLoweringCtx<'tcx> {
    fn default() -> Self {
        Self {
            depth: 0,
            remaining_nodes: MAX_TYPE_LOWERING_NODES,
            produced_nodes: 0,
            produced_budget: produced_node_budget(),
            adt_stack: Vec::new(),
            canonical_cut: trust_types::fx::FxHashSet::default(),
            expand_cut_point: None,
            typing_env: None,
            cache: FxHashMap::default(),
        }
    }
}

impl<'tcx> TyLoweringCtx<'tcx> {
    fn with_typing_env(typing_env: ty::TypingEnv<'tcx>) -> Self {
        Self { typing_env: Some(typing_env), ..Self::default() }
    }
}

/// verifier-coverage: ADT-argument nesting depth above which a
/// speculative alias normalization is likely to overflow rustc's trait
/// solver. Kept deliberately conservative (well below rustc's 128 limit)
/// — see the four documented `E0275` regressions on the `TyKind::Alias`
/// arm of `convert_ty_inner`.
pub(crate) const SAFE_NORMALIZE_ADT_DEPTH: usize = 4;

fn bounded_adt_arg_depth<Node, IsAdt, VisitChildren>(
    root: Node,
    cutoff: usize,
    node_budget: usize,
    mut is_adt: IsAdt,
    mut visit_children: VisitChildren,
) -> usize
where
    Node: Copy + Eq + std::hash::Hash,
    IsAdt: FnMut(Node) -> bool,
    VisitChildren: FnMut(Node, &mut dyn FnMut(Node) -> bool) -> bool,
{
    let mut remaining_nodes = node_budget;
    let mut maximum = 0;
    let mut greatest_depth_seen: FxHashMap<Node, usize> = FxHashMap::default();
    let mut worklist = vec![(root, 0usize)];

    while let Some((current, inherited_depth)) = worklist.pop() {
        if remaining_nodes == 0 {
            return cutoff;
        }
        remaining_nodes -= 1;

        let current_depth = inherited_depth + usize::from(is_adt(current));
        if current_depth >= cutoff {
            return cutoff;
        }
        if greatest_depth_seen.get(&current).is_some_and(|seen| *seen >= current_depth) {
            continue;
        }
        greatest_depth_seen.insert(current, current_depth);
        maximum = maximum.max(current_depth);

        let mut push = |child| {
            // Refuse before an attacker-shaped wide tuple/alias can grow the
            // pending set beyond the deterministic remaining work bound.
            if worklist.len() >= remaining_nodes {
                return false;
            }
            worklist.push((child, current_depth));
            true
        };
        if !visit_children(current, &mut push) {
            return cutoff;
        }
    }

    maximum
}

/// Compute the maximum ADT-argument nesting depth reachable from `ty`
/// without invoking the trait solver.
///
/// This is a pure structural walk over the already-interned `Ty<'tcx>`
/// graph: each `Adt` adds one to the depth, and we recurse into the
/// type-valued generic arguments. Other kinds (references, raw pointers,
/// slices, arrays, tuples, aliases) pass through to their contents
/// without contributing to the depth, because rustc's trait-solver
/// recursion is driven by ADT-argument nesting (e.g. `UInt<UInt<…>>`),
/// not by projection or borrow depth.
///
/// Used as a guard before calling `try_normalize_erasing_regions` on an
/// alias: aliases whose argument types nest ADTs more than
/// `SAFE_NORMALIZE_ADT_DEPTH` levels deep almost always overflow the
/// trait solver, so we leave them `Unsupported` rather than break the
/// build. See `docs/verifier-coverage-roadmap.md` §1.
pub(crate) fn adt_arg_depth<'tcx>(ty: ty::Ty<'tcx>) -> usize {
    // `Ty<'tcx>` is interned: a monomorphic type is a shared-subtree DAG (e.g.
    // `Result<T, T>`, nested `(Tn-1, Tn-1)` tuples, iterator adapter chains from
    // std). A naive structural walk re-descends every shared child once per path
    // that reaches it — O(paths) = exponential in the DAG's node count, even
    // though the distinct-node count is small. This ran during MIR extraction,
    // BEFORE the per-function verification deadline is even armed, so it hung
    // `trustc` for hours at 100% CPU on `memchr(feature="std")` with no solver
    // involved. Memoizing on the interned `Ty` pointer collapses the exponential
    // to linear in distinct subterms.
    //
    // The sole consumer (`normalize_alias`) only tests
    // `depth > SAFE_NORMALIZE_ADT_DEPTH`, so nothing past that threshold is
    // observable. Walk iteratively (no call-stack dependence) and revisit a DAG
    // node only when reached under a strictly larger ADT depth. This is a fresh
    // per-call cap equal to the type lowerer's deterministic 4096-node cap; it
    // does not borrow TyLoweringCtx's mutable counter.
    bounded_adt_arg_depth(
        ty,
        SAFE_NORMALIZE_ADT_DEPTH + 1,
        MAX_TYPE_LOWERING_NODES,
        |current| matches!(current.kind(), TyKind::Adt(..)),
        |current, push| match current.kind() {
            TyKind::Adt(_, args) => args.iter().filter_map(|arg| arg.as_type()).all(push),
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => push(*inner),
            TyKind::Slice(inner) | TyKind::Array(inner, _) => push(*inner),
            TyKind::Tuple(fields) => fields.iter().all(push),
            TyKind::Alias(_, alias_ty) => {
                alias_ty.args.iter().filter_map(|arg| arg.as_type()).all(push)
            }
            _ => true,
        },
    )
}

fn trust_tuple_or_unit(fields: Vec<TrustTy>) -> TrustTy {
    if fields.is_empty() { TrustTy::Unit } else { TrustTy::Tuple(fields) }
}

fn trust_fn_sig_from_rustc<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> FnSig {
    let sig = tcx.instantiate_bound_regions_with_erased(sig);
    FnSig {
        params: sig.inputs().iter().map(|param_ty| convert_ty_inner(tcx, *param_ty, ctx)).collect(),
        ret: Box::new(convert_ty_inner(tcx, sig.output(), ctx)),
    }
}

fn unsupported_ty(kind: impl Into<String>, detail: impl Into<String>) -> TrustTy {
    TrustTy::Unsupported { kind: kind.into(), detail: detail.into() }
}

fn ty_contains_ty<'tcx>(haystack: ty::Ty<'tcx>, needle: ty::Ty<'tcx>) -> bool {
    haystack == needle || haystack.walk().filter_map(|arg| arg.as_type()).any(|ty| ty == needle)
}

fn is_expanding_recursive_adt<'tcx>(
    stack_ty: ty::Ty<'tcx>,
    current_def_id: rustc_hir::def_id::DefId,
    current_args: ty::GenericArgsRef<'tcx>,
) -> bool {
    let TyKind::Adt(stack_adt, stack_args) = stack_ty.kind() else { return false };
    if stack_adt.did() != current_def_id {
        return false;
    }

    current_args.iter().filter_map(|arg| arg.as_type()).any(|current_arg_ty| {
        stack_args.iter().filter_map(|arg| arg.as_type()).any(|stack_arg_ty| {
            current_arg_ty != stack_arg_ty && ty_contains_ty(current_arg_ty, stack_arg_ty)
        })
    })
}

/// Convert a rustc Ty to our simplified Ty.
///
/// This entry point does **not** attempt opaque-alias normalization: an
/// `impl Trait` (`AliasTyKind::Opaque`) type lowers to `Unsupported`. Use
/// it from call sites that do not have a MIR body's `TypingEnv` in scope.
/// To reveal opaque alias types where it is sound and build-safe to do so,
/// use [`convert_ty_in_env`] instead. (`Free` aliases are still expanded.)
// Trust (v25 B1): FAITHFUL-SCALAR extraction mode. When set, isize/usize
// convert to `TrustTy::PtrSizedInt` and char to `TrustTy::Char` instead of
// the legacy width collapse — preserving the identity the trust-ir bridge
// needs for the differential's signature comparison. Thread-local + RAII so
// the flag scopes EXACTLY to one `extract_function_faithful` call even under
// parallel `mir_built` (each rustc worker thread owns its own flag), and the
// legacy verifier path (plain `extract_function`) is byte-identical
// unchanged — its ~700 direct `Ty::Int{..}` matches never see the new
// spellings until their own migration wave.
thread_local! {
    static FAITHFUL_SCALARS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) struct FaithfulScalarsGuard(bool);

impl FaithfulScalarsGuard {
    pub(crate) fn enable() -> Self {
        let prev = FAITHFUL_SCALARS.with(|f| f.replace(true));
        FaithfulScalarsGuard(prev)
    }
}

impl Drop for FaithfulScalarsGuard {
    fn drop(&mut self) {
        let prev = self.0;
        FAITHFUL_SCALARS.with(|f| f.set(prev));
    }
}

fn faithful_scalars() -> bool {
    FAITHFUL_SCALARS.with(|f| f.get())
}

pub(crate) fn convert_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> TrustTy {
    let mut ctx = TyLoweringCtx::default();
    ctx.canonical_cut = canonical_cut_set(tcx, ty);
    convert_ty_inner(tcx, ty, &mut ctx)
}

/// Convert a rustc Ty to our simplified Ty, normalizing **opaque** alias
/// types (`impl Trait`) against `typing_env` where it is sound and
/// build-safe.
///
/// `typing_env` must be the env of the MIR body the type comes from — for
/// verifier purposes that is `body.typing_env(tcx)`, which is
/// `TypingEnv::post_analysis(..)` on the optimized (Runtime-phase) MIR the
/// verifier runs on. Post-analysis is exactly the mode in which rustc
/// reveals an opaque's concrete underlying type within its defining scope,
/// so the reveal is rustc's own canonical normalization rather than a
/// hand-rolled guess.
///
/// Only `AliasTyKind::Opaque` is revealed here. Projection / inherent
/// aliases keep lowering to `Unsupported` — resolving those drives the
/// trait solver, which can fatally overflow rustc's recursion limit (the
/// typenum `UInt<UInt<…>>: Unsigned` regression that defeated four prior
/// normalization attempts). See the alias arm of `convert_ty_inner`.
pub(crate) fn convert_ty_in_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
) -> TrustTy {
    let mut ctx = TyLoweringCtx::with_typing_env(typing_env);
    ctx.canonical_cut = canonical_cut_set(tcx, ty);
    convert_ty_inner(tcx, ty, &mut ctx)
}

fn convert_ty_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // ── R0 REMOVED — THE CUT, at EVERY occurrence including the walk ROOT ────
    //
    // This type lies on a cycle and is the cycle's canonically chosen cut point,
    // so it lowers to the by-name reference NO MATTER which root reached it and
    // NO MATTER whether this occurrence is the outermost nominal position. That
    // last clause is the whole change: the old rule carried the conjunct
    // `!ctx.adt_stack.is_empty()`, which made the representation a function of
    // the ROOT rather than of the type, so one rustc type reached the dump as
    // several `ty_eq`-unequal values (measured on the shipped
    // `structural-fold-corpus/xor_all.json`: `Arc<Tree>` at 1404 bytes as
    // `Tree`'s field and at 2134 bytes as local 6's declared type). The
    // definition is not lost — `record_cut_definition` files it out of band in
    // `VerifiableBody::datatype_defs`, which is what the deletion was always
    // blocked on.
    //
    // The marker is IDENTITY-BEARING (`canonical_cut_ref`, not
    // `recursive_datatype_ref(&erased_name)`): a cut point carries no structure,
    // so an erased marker would make `Foo<u8>` and `Foo<i32>` — two distinct cut
    // points — compare EQUAL wherever both appear. See the merge analysis on the
    // block comment above.
    //
    // BEFORE every budget/depth bail, deliberately. A marker is ONE node and
    // costs nothing to emit, so keeping it canonical under budget pressure is
    // free; only the DEFINITION is skippable, and a marker with no definition
    // declines exactly as it did before the table existed. Emitting the
    // fail-closed `Unsupported` leaf here instead would give one rustc type two
    // spellings again, keyed on how much budget the walk had already spent.
    //
    // `expand_cut_point` is the ONE exception, and it is not a root exemption:
    // it is set only by `cut_point_definition`, for exactly one occurrence of
    // exactly one type, to build that type's own out-of-band definition (`C`
    // unrolled one level with markers at every cut point inside, including `C`).
    if ctx.canonical_cut.contains(&ty) {
        if ctx.expand_cut_point == Some(ty) {
            // One level, once: clear it so a nested re-entry of the SAME type
            // (a self-recursive datatype) still takes the marker arm below.
            ctx.expand_cut_point = None;
        } else {
            let marker = canonical_cut_ref(tcx, ty);
            if let TrustTy::Datatype { name, .. } = &marker {
                let name = name.clone();
                record_cut_definition(tcx, ty, &name, ctx);
            }
            ctx.produced_nodes = ctx.produced_nodes.saturating_add(1);
            return marker;
        }
    }

    // verifier-perf (produced-node budget): once this function's cumulative
    // produced-tree size has crossed the budget, stop assembling fat tree — return
    // the cheap fail-closed recursive-ADT marker. SOUNDNESS: DROP-ONLY (the marker
    // carries no modeled sort; uses still fail closed). See
    // `MAX_TYPE_LOWERING_PRODUCED_NODES`.
    if ctx.produced_nodes > ctx.produced_budget {
        return produced_budget_degraded_leaf();
    }

    // verifier-perf: memoization. If we've already lowered
    // this exact `Ty` in this walk, reuse the result instead of
    // re-walking the subtree and burning the node budget again.
    // rustc interns `Ty<'tcx>` so pointer-equality is the right key.
    // The cache itself is per-`convert_ty` (no global state).
    //
    // RC-1 note: the memo used to need a cut-point bypass, because a cut point's
    // lowering was the full definition at the walk's root and the marker
    // everywhere else — two answers for one key. Under markers-everywhere a cut
    // point returns above and never reaches the memo at all, except on the single
    // `expand_cut_point` occurrence, which runs in its own throwaway sub-context.
    if let Some(cached) = ctx.cache.get(&ty) {
        // verifier-perf: a cache hit still MATERIALIZES the cached subtree (the
        // `clone` copies the whole tree into the parent), so charge its produced
        // size against the budget — otherwise the cache lets an unbounded number of
        // fat-subtree clones bypass the budget (the actual OOM mechanism).
        let cached = cached.clone();
        ctx.produced_nodes = ctx.produced_nodes.saturating_add(produced_node_count(
            &cached,
            ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1),
        ));
        return cached;
    }

    if ctx.depth >= MAX_TYPE_LOWERING_DEPTH {
        return unsupported_ty(
            "TyKind",
            format!("type lowering exceeded depth limit {MAX_TYPE_LOWERING_DEPTH}"),
        );
    }
    if ctx.remaining_nodes == 0 {
        return unsupported_ty(
            "TyKind",
            format!("type lowering exceeded node budget {MAX_TYPE_LOWERING_NODES}"),
        );
    }
    // Ambient per-function deadline (amortized on the node counter): type
    // lowering is the extraction choke point, so polling here bounds every
    // lowering loop by the per-function budget. Bailing to `Unsupported` lets
    // extraction finish fast; the compiler's post-extraction checkpoint then
    // reports the overrun as a hard error. Fail-closed: never a proof.
    if ctx.remaining_nodes % 256 == 0 && trust_types::verify_budget::budget_exhausted() {
        return unsupported_ty(
            "TyKind",
            "type lowering exceeded the per-function verification budget",
        );
    }

    ctx.remaining_nodes -= 1;
    ctx.depth += 1;
    let lowered = match ty.kind() {
        TyKind::Bool => TrustTy::Bool,

        TyKind::Int(int_ty) => {
            // v25 B1 faithful mode: isize keeps its identity for the
            // trust-ir differential lane (legacy path collapses to width).
            if faithful_scalars() && matches!(int_ty, rustc_ast_ir::IntTy::Isize) {
                TrustTy::PtrSizedInt { signed: true }
            } else {
                let width = int_width_from_int_ty(int_ty, tcx);
                TrustTy::Int { width, signed: true }
            }
        }

        TyKind::Uint(uint_ty) => {
            if faithful_scalars() && matches!(uint_ty, rustc_ast_ir::UintTy::Usize) {
                TrustTy::PtrSizedInt { signed: false }
            } else {
                let width = uint_width_from_uint_ty(uint_ty, tcx);
                TrustTy::Int { width, signed: false }
            }
        }

        TyKind::Float(float_ty) => {
            let width = match float_ty {
                rustc_ast_ir::FloatTy::F16 => 16,
                rustc_ast_ir::FloatTy::F32 => 32,
                rustc_ast_ir::FloatTy::F64 => 64,
                rustc_ast_ir::FloatTy::F128 => 128,
            };
            TrustTy::Float { width }
        }

        TyKind::Ref(_, inner_ty, mutability) => TrustTy::Ref {
            mutable: mutability.is_mut(),
            inner: Box::new(convert_ty_inner(tcx, *inner_ty, ctx)),
        },

        TyKind::Slice(elem_ty) => {
            TrustTy::Slice { elem: Box::new(convert_ty_inner(tcx, *elem_ty, ctx)) }
        }

        TyKind::Array(elem_ty, len_const) => {
            let elem = convert_ty_inner(tcx, *elem_ty, ctx);
            // Accept an already-concrete length; otherwise EVALUATE the const so a
            // NAMED length (`[u8; INLINE_SIZE]`), an associated const, etc. lowers.
            // These are idiomatic and monomorphic at verify time, so leaving them
            // "unsupported" wrongly fails panic-freedom on ordinary fixed arrays.
            // Use the body's `TypingEnv` when present, else the fully-monomorphized
            // env (sound here: the array type is part of a concrete, monomorphic body).
            let len = len_const.try_to_target_usize(tcx).or_else(|| {
                let typing_env = ctx.typing_env.unwrap_or_else(ty::TypingEnv::fully_monomorphized);
                tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(*len_const))
                    .ok()
                    .and_then(|c| c.try_to_target_usize(tcx))
            });
            match len {
                Some(len) => TrustTy::Array { elem: Box::new(elem), len },
                // Trust: piece #7a — an un-monomorphized `[T; N]` whose length is a
                // const-generic PARAM gets a MODELED symbolic length keyed on the
                // param identity, instead of falling closed to `unsupported_ty`.
                // The length symbol `__trust_constparam_{index}_{name}` is minted
                // BYTE-IDENTICALLY (via `const_param_symbol`) with the value `N`'s
                // operand symbol, so a guard `if i < N` discharges the bounds VC.
                // SOUNDNESS: keying on `(index, name)` — NOT `(width, signed)` —
                // gives two distinct usize params `M`, `N` DISTINCT symbols, so the
                // guard on `N` cannot discharge an index on `[T; M]` (M != N). Any
                // NON-param unresolved length still fails closed below.
                None => match len_const.kind() {
                    ty::ConstKind::Param(p) => TrustTy::SymArray {
                        elem: Box::new(elem),
                        len_sym: trust_types::ConstLen { index: p.index, name: p.name.to_string() },
                    },
                    _ => unsupported_ty(
                        "TyKind::Array",
                        format!("array length {len_const:?} is not a concrete target usize"),
                    ),
                },
            }
        }

        TyKind::Tuple(fields) => {
            let field_tys: Vec<TrustTy> =
                fields.iter().map(|f| convert_ty_inner(tcx, f, ctx)).collect();
            trust_tuple_or_unit(field_tys)
        }

        TyKind::Adt(adt_def, args) => {
            // SYSROOT-AUTHENTICATED (2026-08-17). This one binding is the name of
            // every emitted `Ty::Adt`/`Ty::Datatype` in this arm AND of the
            // by-name back-edge reference below, so stamping it here keeps the
            // definition and its references on one key. It is the half of the
            // measured `#![no_std]` forgery that the callee stamp cannot reach:
            // the endless iterator is authenticated by
            // `ty_is_authenticated_std_iterator` from this printed root alone.
            let name = crate::sysroot_authenticated_def_path_str(tcx, adt_def.did());
            // R0 REMOVED — the cut arm that used to live HERE, behind the
            // root-relative conjunct `!ctx.adt_stack.is_empty() &&`, has moved to
            // the TOP of this function and lost the conjunct. A cut point never
            // reaches this arm at all any more (except on the single
            // `expand_cut_point` occurrence that builds its own definition), so
            // the paths below see only NON-cut nominal ADTs.
            //
            // Lever A step 2: the kernel universe-`Level` enum lowers to a native
            // recursive `Ty::Datatype` (its `Arc<Level>` children become by-name
            // self-references) instead of degrading to the recursive-ADT
            // `Unsupported` marker. Def-path gated to EXACTLY `Level` (the `Expr`/
            // `ExprKind` datatypes have their own step-5 gates below); `Name` still
            // keeps its existing lowering.
            if is_level_datatype_target(tcx, adt_def.did()) {
                lower_level_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // Lever A step 5: the kernel `ExprKind` ENUM — the structural
            // expression variants the real `infer_type` matches on (BVar/Sort/
            // Const/App/Lam/Pi/Let/Lit/Proj/MData/…) — lowers to a native recursive
            // `Ty::Datatype`. Its recursive `Arc<Expr>` children, and its `Level`/
            // `Name`/`Literal` payloads, become BY-NAME datatype references (see
            // `datatype_child_field_ty`), so the produced tree stays O(variants):
            // the mutually-recursive Expr/ExprKind cluster no longer expands into
            // the ~464 MB `Ty::Adt` tree that OOM-killed extraction. Def-path gated
            // to EXACTLY `ExprKind`, checked BEFORE the enum path below.
            else if is_exprkind_datatype_target(tcx, adt_def.did()) {
                lower_exprkind_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // Lever A step 5: the kernel `Expr` STRUCT (an `ExprKind` plus cached
            // metadata) lowers to a single-constructor `Ty::Datatype` whose `kind`
            // field is a by-name `ExprKind` reference and whose `meta` field is an
            // opaque datatype reference. Checked BEFORE the struct/union path so
            // `Expr` takes the datatype model (and its recursive `kind` child a
            // by-name ref) instead of the recursive-struct field compaction.
            // Def-path gated to EXACTLY `Expr`.
            else if is_expr_datatype_target(tcx, adt_def.did()) {
                lower_expr_datatype(tcx, ty, *adt_def, args, &name, ctx)
            }
            // A UNION lowers like a struct (its real-named overlapping fields via
            // `all_fields()`), NOT like an enum: it has no discriminant, so the
            // enum path's synthetic `__tag` / `__v{v}_` shape is wrong and leaves
            // a union field projection (e.g. `MaybeUninit`'s `value` = Field(1),
            // the `vec!`/`write_box_via_move` write destination) without a sort
            // (`TrustSymbolicAggregateFieldSortMissing`). Modeling the overlapping
            // fields as independent slots is sound for verification here: a
            // single-field-used union (MaybeUninit: write `value`, read `value`)
            // is exact, and a genuine type-punning read (write one field, read
            // another) is still caught by the read-only union-field obligation,
            // which fails closed. So treat structs and unions identically below.
            else if !adt_def.is_struct() && !adt_def.is_union() {
                lower_enum_adt(tcx, ty, *adt_def, args, &name, ctx)
            } else if ctx.adt_stack.contains(&ty) {
                // Lever A (recursive-struct back-edge): re-entering the SAME ADT
                // with identical arguments is the recursive field position (e.g.
                // `Box<Self>`'s pointee resolving back to the struct). Instead of
                // poisoning the whole enclosing type to `Unsupported` — which gave
                // it no modeled SMT sort and forced every projection/match through
                // it to Unknown — emit a BY-NAME datatype reference. SMT-LIB
                // datatypes are natively recursive, so the reference resolves to the
                // definitional occurrence (the outer, fully-lowered type) at declare
                // time. SOUNDNESS: a datatype reference introduces no facts; it is a
                // sort marker only.
                //
                // RETAINED, and it is the one member of the root-relative family
                // that CANNOT be removed — see `TERMINATION FAIL-SAFES` on the block
                // comment above. Whenever the canonical cut set covers the cycle
                // this branch is DEAD (an FVS breaks every cycle, so a cycle is
                // always intercepted by the marker arm at the top of
                // `convert_ty_inner` before the same `ty` can be pushed twice). It
                // fires only where discovery FAILED to see the cycle — R1
                // (`MAX_CANONICAL_CUT_NODES` exceeded, cut set empty) and R2 (a
                // cycle closing through a `TyKind::Alias`, which `nominal_frontier`
                // does not peel) — and there, deleting it is not a canonicity
                // improvement but an unbounded recursion. It stays root-relative
                // exactly on R1/R2, both of which are pre-existing named residuals
                // and neither of which this change claims to remove.
                recursive_datatype_ref(&name)
            } else if ctx
                .adt_stack
                .iter()
                .any(|stack_ty| is_expanding_recursive_adt(*stack_ty, adt_def.did(), args))
            {
                // An EXPANDING generic recursion (`List<Box<List<T>>>`-style, the
                // arguments grow on each re-entry) does NOT have a finite, single
                // SMT datatype sort — the by-name reference would be unsound (the
                // referent's field sorts differ per instantiation). Stay fail-closed:
                // leave it Unsupported (Unknown), never risk a wrong sort. This is
                // the deliberately-left-Unknown case.
                unsupported_ty(
                    "TyKind::Adt",
                    format!(
                        "recursive ADT {name} with expanding generic arguments encountered while lowering fields"
                    ),
                )
            } else {
                // Lever A: compact each oversized field subtree so the enclosing
                // tree cannot blow up to the thousands-of-nodes size that OOM-kills
                // extraction / stalls `place_ty`'s per-place clone. SOUNDNESS: a
                // compacted field is a modeled, fact-free datatype sort — never
                // `Unsupported`, never a fabricated fact.
                //
                // R0 REMOVED (the `cap_fields` half): this gate used to read
                // `cap_fields = !ctx.adt_stack.is_empty()` — compact only inside a
                // nested lowering, keep the full expansion at the TOP level. That
                // made a struct's own field list depend on whether the struct was
                // the walk's ROOT, which is the same root dependence as the cut
                // conjunct one shape over, and it is what the shipped corpus's
                // three spellings of `Tree` actually came from. It is now
                // UNCONDITIONAL, so a field slot is a function of the FIELD TYPE
                // alone (`ty_node_count` of its own lowering against a constant
                // cap) and no longer of how the walk arrived.
                //
                // What the removal costs, recorded rather than hidden (residual R5
                // on the block comment above): compaction is still a decision the
                // PARENT makes about a field, so a type whose own lowering exceeds
                // the cap is a marker as a field and its full self as a local. That
                // is position-relative, not root-relative, and it is fail-CLOSED (a
                // compacted marker has no table entry, so every consumer declines
                // on it). It is also much rarer than it was: under
                // markers-everywhere every recursive tower is already cut to a
                // one-node marker, so the shipped `Arc<Tree>` field measures 15
                // nodes against the cap of 64.
                ctx.adt_stack.push(ty);
                let fields: Vec<(String, TrustTy)> = adt_def
                    .all_fields()
                    .map(|f| {
                        let field_name = f.name.to_string();
                        let mut field_ty =
                            convert_ty_inner(tcx, f.ty(tcx, args).skip_normalization(), ctx);
                        if ty_node_count(&field_ty, MAX_DATATYPE_FIELD_NODES + 1)
                            > MAX_DATATYPE_FIELD_NODES
                        {
                            field_ty = compact_oversized_field(&field_ty);
                        }
                        (field_name, field_ty)
                    })
                    .collect();
                ctx.adt_stack.pop();
                // Trust: PHASE 4 — a struct/union has NO variants; the `fields`
                // are its single anonymous constructor's fields.
                // Trust: enum-disc-full-native — a struct is never disc-index-safe.
                // Trust (B3-4 T3): concrete struct layout, FAITHFUL LANE ONLY —
                // a Some(layout) is semantic-hash-visible, so filling it on a
                // verifier lane would shift shipped proof-cert/content pins
                // (the faithful_enum_repr shield discipline, B3-1). The gates
                // mirror the THIR producer's T2 fill exactly: fully-concrete
                // type, layout_of Ok, offsets in source-declaration order.
                let layout = if faithful_scalars()
                    && !ty.has_non_region_param()
                    && !ty.has_non_region_infer()
                    && !ty.has_opaque_types()
                {
                    ctx.typing_env.and_then(|te| {
                        tcx.layout_of(te.as_query_input(ty)).ok().map(|l| {
                            let r = adt_def.repr();
                            let repr = if r.transparent() {
                                "transparent".to_string()
                            } else if let Some(pack) = r.pack {
                                format!("packed:{}", pack.bytes())
                            } else if r.c() {
                                "c".to_string()
                            } else {
                                "rust".to_string()
                            };
                            Box::new(trust_types::AdtLayoutInfo {
                                size: l.size.bytes(),
                                align: l.align.abi.bytes(),
                                // `FieldsShape::offset` PANICS out of range and a
                                // struct's layout may carry fewer field entries
                                // than the variant has (scalable-vector structs):
                                // bounds-check, never abort the extraction.
                                field_offsets: (0..adt_def.non_enum_variant().fields.len())
                                    .filter(|i| *i < l.layout.fields().count())
                                    .map(|i| l.layout.fields().offset(i).bytes())
                                    .collect(),
                                repr,
                            })
                        })
                    })
                } else {
                    None
                };
                TrustTy::Adt {
                    name,
                    fields,
                    variants: Vec::new(),
                    disc_index_safe: false,
                    faithful_enum_repr: None,
                    layout,
                    enum_layout: None,
                    // Trust: W19 — the struct/union kind, read from rustc's AdtDef.
                    // This is the SOLE faithfulness bearer that lets the field-setter
                    // recognizer's G-STRUCT-KIND gate distinguish a struct (sound
                    // per-field frame) from a UNION (fields overlap at offset 0, the
                    // frame is operationally false). Both structs and unions reach
                    // this arm (the `!is_struct() && !is_union()` enum guard above
                    // routed enums to `lower_enum_adt`), so stamp the real kind.
                    adt_kind: Some(if adt_def.is_union() {
                        trust_types::AdtKind::Union
                    } else {
                        trust_types::AdtKind::Struct
                    }),
                }
            }
        }

        TyKind::Never => TrustTy::Never,

        _ if ty.is_unit() => TrustTy::Unit,

        // Char: legacy verification path maps to u32; the v25 faithful lane
        // preserves char identity for the trust-ir differential.
        TyKind::Char => {
            if faithful_scalars() {
                TrustTy::Char
            } else {
                TrustTy::Int { width: 32, signed: false }
            }
        }

        TyKind::RawPtr(pointee_ty, mutability) => TrustTy::RawPtr {
            mutable: mutability.is_mut(),
            pointee: Box::new(convert_ty_inner(tcx, *pointee_ty, ctx)),
        },

        // Trust: `str` is morally `[u8]` — a fat pointer carrying a byte length.
        // Modeling it as Slice<u8> reuses the existing slice encoding (same
        // Sort::Int fallback, same fat-pointer classification) so the type walk
        // stops emitting a spurious UnsupportedMir obligation for trivially-safe
        // string code. Real per-statement safety VCs are unaffected.
        TyKind::Str => {
            // Trust (B2-2): the FAITHFUL lane keeps `str` DISTINCT from `[u8]` so the
            // trust-ir bridge can spell `&str` as the format's first-class
            // FatPtr(FatPtrKind::Str), structurally equal to the producer's. The
            // legacy verifier lane keeps the historical Slice{u8} conflation
            // byte-identically (same guard discipline as the B1 scalar spellings).
            if faithful_scalars() {
                TrustTy::Str
            } else {
                TrustTy::Slice { elem: Box::new(TrustTy::Int { width: 8, signed: false }) }
            }
        }
        TyKind::Foreign(def_id) => unsupported_ty(
            "TyKind::Foreign",
            format!(
                "extern type {} is opaque to Rust layout",
                crate::safe_def_path_str(tcx, *def_id)
            ),
        ),
        TyKind::FnDef(def_id, args) => {
            let sig = tcx.fn_sig(*def_id).instantiate(tcx, args).skip_normalization();
            TrustTy::FnDef {
                name: crate::sysroot_authenticated_def_path_str(tcx, *def_id),
                sig: Box::new(trust_fn_sig_from_rustc(tcx, sig, ctx)),
            }
        }
        TyKind::FnPtr(..) => {
            TrustTy::FnPtr { sig: Box::new(trust_fn_sig_from_rustc(tcx, ty.fn_sig(tcx), ctx)) }
        }
        TyKind::Dynamic(predicates, _) => TrustTy::Dynamic {
            trait_name: predicates
                .principal_def_id()
                .map(|def_id| crate::sysroot_authenticated_def_path_str(tcx, def_id))
                .unwrap_or_else(|| "dyn".to_string()),
        },
        TyKind::Closure(def_id, args) => {
            let clo = args.as_closure();
            // Trust (B6, RFC TRUST_IR_V2): record the closure's CALL signature +
            // inferred kind so the trust-ir bridge can spell a by-value FnOnce env
            // as the format's first-class Ty::Closure, structurally equal to the
            // producer's. `params` are the UNTUPLED call arguments; a unit return
            // is `None` (the producer's empty-returns convention). An unresolved
            // kind (`kind_ty` still an inference placeholder — impossible for the
            // monomorphic bodies this crate extracts, but never assumed) or a
            // non-tuple input leaves `call: None` — the respell then fails closed
            // to the closure_env struct spelling.
            let call = clo.kind_ty().to_opt_closure_kind().and_then(|k| {
                let sig = tcx.instantiate_bound_regions_with_erased(clo.sig());
                let rustc_middle::ty::TyKind::Tuple(arg_tys) = sig.inputs().first()?.kind() else {
                    return None;
                };
                Some(Box::new(trust_types::ClosureCallSig {
                    kind: match k {
                        rustc_middle::ty::ClosureKind::Fn => trust_types::ClosureCallKind::Fn,
                        rustc_middle::ty::ClosureKind::FnMut => trust_types::ClosureCallKind::FnMut,
                        rustc_middle::ty::ClosureKind::FnOnce => {
                            trust_types::ClosureCallKind::FnOnce
                        }
                    },
                    params: arg_tys.iter().map(|a| convert_ty_inner(tcx, a, ctx)).collect(),
                    ret: (!sig.output().is_unit())
                        .then(|| convert_ty_inner(tcx, sig.output(), ctx)),
                }))
            });
            TrustTy::Closure {
                name: crate::sysroot_authenticated_def_path_str(tcx, *def_id),
                upvars: clo
                    .upvar_tys()
                    .iter()
                    .map(|upvar_ty| convert_ty_inner(tcx, upvar_ty, ctx))
                    .collect(),
                call,
            }
        }
        TyKind::CoroutineClosure(def_id, _) => unsupported_ty(
            "TyKind::CoroutineClosure",
            format!(
                "coroutine closure {} needs state-machine modeling",
                crate::safe_def_path_str(tcx, *def_id)
            ),
        ),
        // Trust: piece #13 (safe-async data-safety) — model a coroutine frame
        // as an OPAQUE type (`Ty::Coroutine`), like a closure, rather than
        // `Ty::Unsupported`. This is what lets a coroutine RESUME body (post-
        // `StateTransform`) verify its ordinary arithmetic/bounds segments: the
        // resume body's `self` frame is `TyKind::Coroutine`, and the state
        // selector / across-await frame fields read out of it resolve OPAQUELY.
        //
        // Trust: piece #13 step-2 — carry the coroutine's UPVAR types (the
        // captured args, which occupy the frame's PREFIX field slots and are what
        // a zero-await resume body reads back, e.g. `((*self).0: u8)` = the saved
        // arg `x`). This is the SAME `upvar_tys()` a closure carries. SOUNDNESS is
        // preserved on BOTH lanes:
        //   * vcgen/default lane: its `project_ty`/`project_ty_ref` `Field` arms
        //     have NO `Ty::Coroutine` case (only `Ty::Closure`), so a coroutine
        //     frame-field projection STILL returns `None` there → still havoc'd,
        //     unchanged from the empty-upvars behavior (the across-await staleness
        //     trap is unaffected).
        //   * native trust-ir-bridge lane: it now resolves the field TYPE from
        //     these upvars, but the frame VALUE is built as an opaque `Inst::Undef`
        //     (piece #13 step-2 aggregate lowering), so an `ExtractField` off it
        //     yields a FRESH UNCONSTRAINED value — the field TYPE is precise but
        //     the field VALUE is havoc'd, exactly the sound over-approximation for
        //     "anything the executor left across a suspend". A value held across
        //     `.await` therefore never carries a stale pre-suspend fact.
        // Only the captured-arg prefix fields are typed here; a HIGHER field
        // (an across-await saved local, only reached in a body with an `.await`)
        // has no upvar entry and the native lane fails that projection closed
        // (Unknown, never a false proof) — the single/multi-await frontier is a
        // sound later increment.
        TyKind::Coroutine(def_id, args) => TrustTy::Coroutine {
            name: crate::sysroot_authenticated_def_path_str(tcx, *def_id),
            upvars: args
                .as_coroutine()
                .upvar_tys()
                .iter()
                .map(|upvar_ty| convert_ty_inner(tcx, upvar_ty, ctx))
                .collect(),
        },
        TyKind::CoroutineWitness(def_id, _) => TrustTy::Coroutine {
            name: crate::sysroot_authenticated_def_path_str(tcx, *def_id),
            upvars: Vec::new(),
        },
        TyKind::Pat(inner_ty, _pat) => {
            // verifier-perf: pattern types (`u32 is 1..`, NonZeroUsize,
            // etc.) are *restricted-value subsets* of an underlying integer
            // type. Lowering as the inner type is sound for safety
            // obligations: any overflow/bounds/cast check that holds on the
            // wider integer also holds on the restricted subset. The
            // restriction itself is preserved by rustc's MIR-level
            // construction (a `Pat` literal can only be produced through
            // checked entry points), so the verifier still has correct
            // semantics — it just doesn't *additionally* exploit the
            // refinement yet. Following work: emit a `TrustRefinement::Range`
            // precondition so the SMT backend can use the tighter bound.
            convert_ty_inner(tcx, *inner_ty, ctx)
        }
        TyKind::Alias(_, alias) => {
            // Trust: rust 1.99 moved the `AliasTyKind` off `TyKind::Alias`'s first
            // payload (now `IsRigid`) onto the `AliasTy`'s `kind` field; the alias
            // `def_id` likewise lives inside that per-variant `kind`.
            let kind = alias.kind;
            // verifier-perf: keep solver-dependent alias
            // normalization fail-closed.
            //
            // FOUR attempts to call `tcx.try_normalize_erasing_regions`
            // here ALL caused typenum's `UInt<UInt<…>>: Unsigned` trait
            // resolution to exhaust rustc's 128-deep recursion limit and
            // fail with `E0275`:
            //   1. Unconditional normalize          → E0275
            //   2. Guard on "no nested Alias args"  → E0275 (typenum
            //      nesting is in ADT args, not Alias args)
            //   3. Guard on adt_arg_depth ≤ 16      → E0275 in libstd
            //      test compile (zlib-rs deps)
            //   4. Guard on adt_arg_depth ≤ 4       → E0275 in libstd
            //      test compile *during* the stage2 build itself
            //
            // The trait solver's recursion budget is exhausted by
            // something we trigger via the normalize call — not the
            // alias arg depth alone. Diagnosis is open; the path
            // forward is documented in
            // `docs/verifier-coverage-roadmap.md` §1.
            //
            // Definitionally transparent free type aliases are different:
            // rustc exposes a structural expander that substitutes the
            // alias RHS without solving projection/inherent associated-type
            // obligations. That is safe to use here because unsupported
            // constructs in the expanded RHS still flow through the normal
            // fail-closed lowering path.
            match kind {
                ty::AliasTyKind::Free { def_id } => {
                    let expanded = tcx.expand_free_alias_tys(
                        tcx.type_of(def_id).instantiate(tcx, alias.args).skip_normalization(),
                    );
                    convert_ty_inner(tcx, expanded, ctx)
                }
                // verifier-coverage: reveal `impl Trait` (opaque)
                // aliases to their concrete underlying type, but only when
                // we have the body's `TypingEnv` (i.e. we came in through
                // `convert_ty_in_env`). The reveal goes through a
                // `tcx.type_of` def lookup folded by
                // `try_normalize_erasing_regions`, NOT the trait selector,
                // so it does not re-trigger the typenum `E0275` overflow
                // that Projection/Inherent resolution does. Without an env,
                // stay fail-closed (legacy behavior).
                ty::AliasTyKind::Opaque { .. } => match ctx.typing_env {
                    Some(typing_env) => normalize_alias(tcx, typing_env, ty, ctx),
                    None => unsupported_ty(
                        "TyKind::Alias",
                        "opaque alias has no typing env to reveal against".to_string(),
                    ),
                },
                // Trust verifier-coverage: resolve monomorphic Projection/Inherent
                // associated types (e.g. a `File` fd modeled as `<_ as _>::Assoc`)
                // to their concrete underlying type through the SAME guarded
                // normalizer the Opaque arm uses. `normalize_alias`'s
                // `has_non_region_param` + `adt_arg_depth` guards reject exactly the
                // pre-monomorphization and deep-typenum (`UInt<UInt<…>>: Unsigned`)
                // cases that overflowed the trait solver (E0275) in the four prior
                // projection-normalization attempts (see the FOUR-attempts note at
                // the top of this match). Without an env, stay fail-closed.
                ty::AliasTyKind::Projection { .. } | ty::AliasTyKind::Inherent { .. } => {
                    match ctx.typing_env {
                        Some(typing_env) => normalize_alias(tcx, typing_env, ty, ctx),
                        None => unsupported_ty(
                            "TyKind::Alias",
                            format!("alias type {kind:?} has no typing env to normalize against"),
                        ),
                    }
                }
            }
        }
        TyKind::Param(param) => unsupported_ty(
            "TyKind::Param",
            format!("generic parameter {param:?} needs monomorphization"),
        ),
        TyKind::Bound(_, bound) => {
            unsupported_ty("TyKind::Bound", format!("bound type {bound:?} needs binder semantics"))
        }
        TyKind::Placeholder(placeholder) => unsupported_ty(
            "TyKind::Placeholder",
            format!("placeholder type {placeholder:?} needs canonical-query semantics"),
        ),
        TyKind::Infer(infer) => unsupported_ty(
            "TyKind::Infer",
            format!("inference variable {infer:?} was not resolved"),
        ),
        TyKind::UnsafeBinder(_) => unsupported_ty(
            "TyKind::UnsafeBinder",
            "unsafe binder type needs erased-lifetime semantics",
        ),
        TyKind::Error(_) => {
            unsupported_ty("TyKind::Error", "rustc reported an erroneous type during extraction")
        }
    };
    ctx.depth -= 1;
    // verifier-perf (produced-node budget): charge the produced size of this
    // freshly-lowered subtree (short-circuited just past the remaining headroom so
    // a huge tree costs O(headroom)). When the cumulative produced size crosses the
    // budget, the early-return at the top of `convert_ty_inner` degrades every
    // subsequent lowering to the fail-closed marker (DROP-ONLY).
    let headroom = ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1);
    ctx.produced_nodes = ctx.produced_nodes.saturating_add(produced_node_count(&lowered, headroom));
    if ctx.produced_nodes > ctx.produced_budget && std::env::var("TRUST_VCGEN_TRACE_BUDGET").is_ok()
    {
        eprintln!(
            "[TYPE_LOWERING_BUDGET] produced-node budget {} crossed (produced={}) — degrading remaining types to fail-closed Unsupported",
            ctx.produced_budget, ctx.produced_nodes,
        );
    }
    // verifier-perf: cache the result so subsequent walks
    // through the same Ty hit the early-return at the top.
    // RC-1: a cut point never gets here except on its single `expand_cut_point`
    // occurrence, and that runs in a throwaway sub-context whose memo dies with
    // it — so caching is unconditional again.
    ctx.cache.insert(ty, lowered.clone());
    lowered
}

/// Normalize a monomorphic **opaque** (`impl Trait`), **projection**
/// (`<T as Trait>::Assoc`), or **inherent** alias to its concrete underlying
/// type and lower that, or return `Unsupported` if it cannot be resolved to a
/// supported sort.
///
/// Invoked only when a `typing_env` is present (i.e. we came in through
/// [`convert_ty_in_env`]). The resolution goes through rustc's own
/// `try_normalize_erasing_regions`, so:
///
/// * In PostAnalysis mode (Runtime-phase MIR — what the verifier runs on)
///   the alias resolves to its real concrete type within its defining
///   scope. We then lower *that* type. This is semantics-preserving: the
///   value at this local genuinely has the resolved type at runtime.
/// * If the env is not one that resolves this alias (e.g. an opaque outside
///   its defining scope, so normalization leaves it as an alias), or
///   normalization returns an error type, or the resolved type is itself
///   another alias, or it lowers to `Unsupported`, we fail safe and return
///   `Unsupported`. A false-`Unsupported` only costs proof coverage; mapping
///   an alias to a wrong sort would be unsound.
///
/// Build-safety guards (the two the four prior projection-normalization
/// attempts lacked — see the FOUR-attempts note on the `TyKind::Alias` arm):
///
/// * `has_non_region_param()`: only fully-monomorphic aliases are normalized.
///   A param-bearing projection is pre-monomorphization — its associated type
///   is not knowable here, and feeding it to the normalizer is exactly the
///   `UInt<UInt<…>>: Unsigned` shape that overflowed the trait solver (E0275).
/// * `adt_arg_depth(ty) <= SAFE_NORMALIZE_ADT_DEPTH`: a deeply-nested ADT
///   argument (typenum-like) can re-enter the fatal trait-solver recursion
///   when projection resolution folds the alias's generic arguments. The
///   shallow-depth guard keeps such an alias `Unsupported` rather than risking
///   the overflow.
///
/// Together these bound the projection path to monomorphic, shallow aliases
/// that resolve in O(1) without deep selector recursion — never a guess, only
/// rustc's definitional-equal concrete type or a fail-safe `Unsupported`.
fn normalize_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    alias_ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // Only normalize fully-monomorphic aliases. If the alias (or its args)
    // still carries a non-region generic parameter, the body is generic /
    // pre-monomorphization: the underlying type is not knowable here, and
    // feeding a param-bearing type to `normalize_erasing_regions` is the case
    // the rest of this crate guards against (cf. `const_operand_value`). Stay
    // Unsupported — fail safe.
    if alias_ty.has_non_region_param() {
        // Trust (R3, generics): this marker is the PRODUCER of the shared
        // `trust_types::PRE_MONO_ALIAS_{KIND,DETAIL}` pair — the vcgen
        // declaration relaxation and the bridge's opaque zero-field-struct
        // lowering key on EXACTLY this (kind, detail). Keep them in lockstep.
        return unsupported_ty(
            trust_types::PRE_MONO_ALIAS_KIND,
            trust_types::PRE_MONO_ALIAS_DETAIL,
        );
    }

    let depth = adt_arg_depth(alias_ty);
    if depth > SAFE_NORMALIZE_ADT_DEPTH {
        return unsupported_ty(
            "TyKind::Alias",
            format!("alias args nest ADTs too deep ({depth}) to normalize safely"),
        );
    }

    // rustc's canonical normalization. `try_*` (not the panicking variant) so a
    // normalization failure is a graceful `Err`, never a panic. The
    // monomorphism + depth guards above keep this off the typenum E0275 path.
    let revealed =
        match tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(alias_ty)) {
            Ok(revealed) => revealed,
            Err(_) => {
                return unsupported_ty(
                    "TyKind::Alias",
                    "alias could not be normalized in this typing env".to_string(),
                );
            }
        };

    // If normalization made no progress (still the same alias, or resolved
    // to *another* alias — e.g. an opaque not in its defining scope), do not
    // loop or guess: stay Unsupported.
    if revealed == alias_ty || matches!(revealed.kind(), TyKind::Alias(..)) {
        return unsupported_ty(
            "TyKind::Alias",
            "alias did not resolve to a concrete underlying type here".to_string(),
        );
    }

    // Lower the concrete revealed type. Any downstream `Unsupported`
    // (including a `TyKind::Error` from a non-fatal overflow `delay_as_bug`)
    // propagates as-is, so we never upgrade an unprovable type to a
    // provable-looking sort.
    convert_ty_inner(tcx, revealed, ctx)
}

/// Lever A step 2 — pure predicate: is `(crate_name, def_path)` the kernel
/// universe-`Level` enum? Gated on the crate NAME being `clean_kernel` AND the
/// def path being exactly `level::Level`, handling BOTH `def_path_str` renderings:
///   * upstream dependency  → `clean_kernel::level::Level` (crate-name prefixed)
///   * crate under compile  → `level::Level` (LOCAL defs render without the crate
///     name — the real path observed extracting `Level` from the kernel crate
///     itself; verified in-test via the `probe`).
/// The crate-name guard makes the bare `level::Level` form precise (a same-named
/// `level::Level` in another crate is rejected), and exact-match (not suffix)
/// rejects `…sublevel::Level`. EXACTLY `Level` un-degrades to a `Ty::Datatype`
/// this step; every other recursive ADT (`Name`, `Expr`, …) keeps its existing
/// lowering. Pure INFRASTRUCTURE — proves no VC, drains no axiom.
fn is_level_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::level::Level" || def_path == "level::Level")
}

/// `tcx`-driven form of [`is_level_path`]: reads the ADT's owning crate name and
/// its def path. Scoping to a single crate+path keeps the change faithful and
/// auditable — no other type's lowering shifts.
fn is_level_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_level_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// Lever A step 5 — is `(crate_name, def_path)` the kernel `Expr` STRUCT (the
/// `ExprKind` + cached-metadata wrapper that the whole kernel passes around)?
/// Same crate-name guard + both `def_path_str` renderings as [`is_level_path`].
/// `Expr` is defined in module `expr` (`expr/mod.rs`), so its def path is
///   * upstream dependency  → `clean_kernel::expr::Expr`
///   * crate under compile  → `expr::Expr`
/// Exact match (not suffix) rejects `…exprkind::Expr` or a same-named `Expr` in
/// another module/crate. Pure INFRASTRUCTURE — proves no VC, drains no axiom.
fn is_expr_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::expr::Expr" || def_path == "expr::Expr")
}

/// Lever A step 5 — is `(crate_name, def_path)` the kernel `ExprKind` ENUM (the
/// structural expression variants the real `infer_type` matches on)? `ExprKind`
/// is defined in module `expr::kind` (`expr/kind.rs`), so its def path is
///   * upstream dependency  → `clean_kernel::expr::kind::ExprKind`
///   * crate under compile  → `expr::kind::ExprKind`
/// Same crate-name guard + exact-match discipline as [`is_expr_path`].
fn is_exprkind_path(crate_name: &str, def_path: &str) -> bool {
    crate_name == "clean_kernel"
        && (def_path == "clean_kernel::expr::kind::ExprKind" || def_path == "expr::kind::ExprKind")
}

/// `tcx`-driven form of [`is_expr_path`].
fn is_expr_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_expr_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// `tcx`-driven form of [`is_exprkind_path`].
fn is_exprkind_datatype_target(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    is_exprkind_path(tcx.crate_name(def_id.krate).as_str(), &crate::safe_def_path_str(tcx, def_id))
}

/// The nominal-ADT paths that are TRANSPARENT heap/pointer indirections for the
/// purpose of the datatype model: a recursive child stored behind one of these
/// (`Succ(Arc<Level>)`) is semantically just the pointee datatype. Peeled by
/// [`peel_transparent_pointers`] so a recursive field models as a direct datatype
/// self-reference rather than a fat `Arc`/`Box`/`Rc` wrapper subtree.
fn is_transparent_pointer_wrapper(name: &str) -> bool {
    matches!(
        name,
        "alloc::sync::Arc"
            | "std::sync::Arc"
            | "alloc::rc::Rc"
            | "std::rc::Rc"
            | "alloc::boxed::Box"
            | "std::boxed::Box"
    )
}

/// Peel transparent references/raw pointers and `Arc`/`Rc`/`Box` wrappers off a
/// field type to reach the nominal pointee type. `Succ(Arc<Level>)`'s field peels
/// to `Level`; `Param(Name)`'s field is already nominal and peels to itself.
/// Bounded by `MAX_TYPE_LOWERING_DEPTH` so a pathological chain cannot loop.
fn peel_transparent_pointers<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    let mut cur = ty;
    for _ in 0..MAX_TYPE_LOWERING_DEPTH {
        match cur.kind() {
            TyKind::Ref(_, inner, _) => cur = *inner,
            TyKind::RawPtr(inner, _) => cur = *inner,
            TyKind::Adt(def, args)
                if is_transparent_pointer_wrapper(&crate::sysroot_authenticated_def_path_str(
                    tcx,
                    def.did(),
                )) =>
            {
                match args.types().next() {
                    Some(inner) => cur = inner,
                    None => return cur,
                }
            }
            _ => return cur,
        }
    }
    cur
}

/// Model one datatype variant/constructor field (Lever A, shared by `Level`
/// step 2 and `Expr`/`ExprKind` step 5). A field whose peeled core is a nominal
/// ADT — a recursive self-reference reached through `Arc`/`Box`/`Rc`/`&`/`*`
/// (`App(Arc<Expr>, Arc<Expr>)`, `Succ(Arc<Level>)`), or a sibling nominal payload
/// (`Sort`'s `Level`, `Const`/`Proj`/`Param`'s `Name`, `Lit`'s `Literal`,
/// `Lam`'s `BinderData`, `Expr`'s `ExprMeta`) — becomes a BY-NAME `Ty::Datatype`
/// reference: for the type itself this is the recursive back-edge; for a sibling
/// datatype (`Level`) it is the cross-reference resolved at declare time; for a
/// type NOT modeled as a datatype this step (`Name`, `Literal`, `BinderData`,
/// `ExprMeta`) it is the deliberately OPAQUE, fact-free datatype sort. A non-ADT
/// core (`BVar`'s `u32`, `Let`'s `bool`) lowers normally through
/// `convert_ty_inner`. THIS is the mechanism that dodges the 464 MB blow-up: a
/// recursive/nominal child is an O(1) by-name ref, never a full re-expansion.
/// SOUNDNESS: a by-name datatype reference asserts nothing — it is a sort marker
/// only (see `Ty::Datatype`'s doc).
fn datatype_child_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    field_ty: ty::Ty<'tcx>,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    let core = peel_transparent_pointers(tcx, field_ty);
    match core.kind() {
        TyKind::Adt(core_def, _) => {
            recursive_datatype_ref(&crate::sysroot_authenticated_def_path_str(tcx, core_def.did()))
        }
        _ => convert_ty_inner(tcx, field_ty, ctx),
    }
}

/// Lever A step 2 — lower the kernel universe-`Level` enum to a native SMT-LIB
/// `Ty::Datatype` with its real five constructors: `Zero` (no fields), `Succ`
/// (one `Level`), `Max`/`IMax` (two `Level`), `Param` (one opaque `Name`). The
/// recursive `Level` children (stored behind `Arc<Level>` = `LevelArc`) model as
/// by-name datatype self-references (see `level_field_ty`), so the datatype is
/// finitely declarable in the standard datatype theory. This REPLACES the
/// recursive-ADT `Unsupported` degrade for `Level` ONLY (def-path gated).
///
/// SOUNDNESS: a datatype declaration introduces only the standard, sound
/// constructor/selector/tester/injectivity/acyclicity axioms; a fresh
/// `Level`-sorted constant is unconstrained, so it can never vacuously discharge
/// an obligation (false-prove). Faithful lowering — real variant structure, not a
/// stub.
fn lower_level_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A step 5 — lower the kernel `ExprKind` enum to a native recursive
/// `Ty::Datatype` with one constructor per variant (BVar/Sort/Const/App/Lam/Pi/
/// Let/Lit/Proj/MData/SProp/Squash/Cubical*/ZFC*). Recursive `Arc<Expr>` children
/// and `Level`/`Name`/`Literal`/`BinderData` payloads model as BY-NAME datatype
/// references (see `datatype_child_field_ty`), so the produced tree is O(variants)
/// with NO expansion of the Expr/ExprKind cluster. This REPLACES the recursive-ADT
/// `Unsupported`/produced-node-budget degrade for `ExprKind` ONLY (def-path gated).
/// SOUNDNESS: a datatype declaration introduces only the standard sound
/// constructor/selector/tester/injectivity/acyclicity axioms; a fresh
/// `ExprKind`-sorted constant is unconstrained, so it can never vacuously discharge
/// an obligation. Faithful lowering — the real variant structure, not a stub.
fn lower_exprkind_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A step 5 — lower the kernel `Expr` struct to a single-constructor
/// `Ty::Datatype` (a struct is a one-variant ADT in rustc's model) whose `kind`
/// field is a by-name `ExprKind` reference and whose `meta` field is an opaque
/// `ExprMeta` datatype reference. The by-name `kind` ref is the OTHER half of the
/// Expr/ExprKind mutual recursion — with both refs by-name, neither type expands
/// the other, so the cluster stays finitely declarable. Def-path gated to `Expr`.
/// SOUNDNESS: identical to `lower_exprkind_datatype` — a sound datatype
/// declaration, faithful single-constructor structure.
fn lower_expr_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    lower_adt_as_datatype(tcx, ty, adt_def, args, name, ctx)
}

/// Lever A — the shared core that lowers ANY nominal ADT (enum OR struct) to a
/// native SMT-LIB `Ty::Datatype`: one constructor per `adt_def.variants()` entry
/// (a struct yields exactly one, named after the struct), each constructor's
/// fields modeled by `datatype_child_field_ty` (recursive/nominal children →
/// by-name refs, scalars → their concrete sort). Backs `lower_level_datatype`
/// (step 2) and `lower_expr_datatype`/`lower_exprkind_datatype` (step 5).
///
/// The by-name child refs keep the produced tree O(variants), so the
/// mutually-recursive Expr/ExprKind/Level cluster is finitely declarable and
/// never blows up (the 464 MB `Ty::Adt` expansion is dodged). SOUNDNESS: a
/// datatype declaration introduces only the standard sound datatype-theory
/// axioms; a fresh datatype-sorted constant is unconstrained.
fn lower_adt_as_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    // Back-edge guard (defensive): if this type is already being lowered on this
    // walk, emit the by-name self-reference rather than re-expanding. In practice
    // `datatype_child_field_ty` peels recursive children to refs WITHOUT
    // re-entering, so the type is never pushed twice — this only backstops an
    // unexpected reach. RETAINED for the same reason as the struct arm's guard: a
    // TERMINATION fail-safe, dead whenever the canonical cut covers the cycle.
    if ctx.adt_stack.contains(&ty) {
        return recursive_datatype_ref(name);
    }
    ctx.adt_stack.push(ty);
    let mut variants: Vec<(String, Vec<(String, TrustTy)>)> = Vec::new();
    for variant in adt_def.variants().iter() {
        let mut variant_fields: Vec<(String, TrustTy)> = Vec::new();
        for field in variant.fields.iter() {
            let modeled =
                datatype_child_field_ty(tcx, field.ty(tcx, args).skip_normalization(), ctx);
            variant_fields.push((field.name.to_string(), modeled));
        }
        variants.push((variant.name.to_string(), variant_fields));
    }
    ctx.adt_stack.pop();
    TrustTy::Datatype { name: name.to_string(), variants }
}

fn lower_enum_adt<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    name: &str,
    ctx: &mut TyLoweringCtx<'tcx>,
) -> TrustTy {
    if ctx.adt_stack.contains(&ty) {
        // Lever A (recursive-enum back-edge): the enum re-enters itself at a
        // variant field (e.g. `Expr` reached through a variant's `Box<Expr>`).
        // Emit a BY-NAME datatype reference rather than poisoning the enclosing
        // type to `Unsupported`. The OUTER (first) occurrence — already on the
        // stack — carries the full flat `Ty::Adt` (`__tag` + `__v{v}_…`) shape the
        // existing enum/discriminant machinery understands; this back-edge only
        // needs a modeled SMT sort so the field's place resolves a sort and no
        // longer goes Unknown. SOUNDNESS: a datatype reference asserts nothing.
        //
        // RETAINED as a TERMINATION fail-safe, like the struct arm's twin: an FVS
        // breaks every cycle, so whenever discovery saw the cycle this enum is
        // intercepted by the marker arm at the top of `convert_ty_inner` and can
        // never be pushed twice. It fires only on residuals R1 (discovery bound)
        // and R2 (alias-mediated cycle), where removing it means unbounded
        // recursion rather than better canonicity.
        return recursive_datatype_ref(name);
    }
    // Lever A (field compaction gate) — mirrors the struct path above, and like
    // it this gate is now UNCONDITIONAL.
    //
    // R0 REMOVED (the `cap_fields` half): it used to read `cap_fields =
    // !ctx.adt_stack.is_empty()`, i.e. compact an oversized variant field only
    // inside a nested lowering and keep the flat expansion at the top level. That
    // made ONE enum type lower two ways depending on whether it was the walk's
    // root, which is exactly the divergence this change exists to remove.
    //
    // The historical reason for the gate was that an unconditional cap
    // "compacted such payloads to by-name `Ty::Datatype` references, regressing
    // whole functions to Unknown in the native lane". That measurement PREDATES
    // the canonical cut: the payload subtrees it was protecting were fat because
    // recursive Arc/ArcInner towers expanded inside them, and under
    // markers-everywhere every such tower is a one-node marker before the cap can
    // see it (measured on the shipped corpus: `Arc<Tree>` = 15 nodes against a cap
    // of 64). A payload that still exceeds 64 nodes is a genuinely large acyclic
    // aggregate, and compacting it is the SOFT degradation — the alternative when
    // the produced-node budget below trips is the whole enum bailing to the
    // fail-closed `Unsupported` leaf, which is strictly worse.
    ctx.adt_stack.push(ty);

    let mut fields = Vec::new();
    // 1. Add discriminant
    fields.push(("__tag".to_string(), TrustTy::Int { width: pointer_width(tcx), signed: true }));

    // Trust: PHASE 4 — build the per-variant constructor view ALONGSIDE the
    // existing flattened union `fields`. Each `VariantDef` carries the variant's
    // real discriminant tag (the value a `SwitchInt` compares against) plus its
    // OWN field list (each variant's fields named by their source name, or the
    // positional index for tuple variants), so `trust-clean` can reflect a real
    // multi-constructor inductive. The flattened `fields` view below is RETAINED
    // verbatim so no pre-P4 consumer (sort lookup, field projection) changes.
    let mut variants: Vec<trust_types::VariantDef> = Vec::new();
    // Trust (B3-1): a compacted (by-name-ref) variant field disqualifies the
    // faithful first-class spelling — the def would not be structurally equal
    // to the producer's.
    let mut compacted = false;

    // 2. Flatten all variants (existing union view) + populate per-variant defs.
    for (v_idx, variant) in adt_def.variants().iter_enumerated() {
        // verifier-perf (produced-node budget): bail the WHOLE enum to the
        // fail-closed recursive-ADT marker once the per-function produced-tree size
        // crosses the budget. This is the load-bearing cap for the
        // `Ty::clone`-in-the-flattened-fields-loop explosion (each `field_ty.clone()`
        // below deep-copies a recursive `Ty::Adt`, and a mutually-recursive enum
        // cluster multiplies these into a ~464 MB tree that OOM-kills extraction). By
        // bailing BEFORE accumulating more variants, the enum's retained size is
        // bounded. SOUNDNESS: DROP-ONLY — the marker carries no modeled SMT sort, so a
        // value USE still fails closed; never a false PROVE. See
        // `MAX_TYPE_LOWERING_PRODUCED_NODES`.
        if ctx.produced_nodes > ctx.produced_budget {
            ctx.adt_stack.pop();
            return produced_budget_degraded_leaf();
        }
        let mut variant_fields: Vec<(String, TrustTy)> = Vec::new();
        for field in &variant.fields {
            let mut field_ty = convert_ty_inner(tcx, field.ty(tcx, args).skip_normalization(), ctx);
            // Lever A (field compaction): a recursive enum reached through `Arc`/
            // `Box` (clean-kernel's `Expr`/`ExprKind`/`Level`) has variant fields
            // that flatten — via Arc/ArcInner/Atomic/UnsafeCell wrappers — into `Ty`
            // subtrees of HUNDREDS-to-THOUSANDS of nodes. COMPACT any oversized
            // field subtree to its by-name datatype reference so the ENCLOSING enum
            // stays MODELED (a real `Ty::Adt` whose fat field is now a small
            // datatype-sort marker) instead of bailing the whole enum to the
            // fail-closed `produced_budget_degraded_leaf` — which is exactly what
            // unlocks the Lever-A datatype-sort coverage win. SOUNDNESS: a compacted
            // field is a modeled, fact-free datatype sort (see
            // `compact_oversized_field`); only precision vs. tractability trades off,
            // never soundness, and the small scalar payloads keep full detail.
            if ty_node_count(&field_ty, MAX_DATATYPE_FIELD_NODES + 1) > MAX_DATATYPE_FIELD_NODES {
                field_ty = compact_oversized_field(&field_ty);
                compacted = true;
            }
            // verifier-perf (produced-node budget): charge the flattened-view clone we
            // are about to make (the `field_ty.clone()` deep-copies the produced
            // subtree — the actual OOM allocation). Once the budget is crossed, stop
            // duplicating fat subtrees and bail the enum to the fail-closed marker.
            // (A compacted field is now tiny, so this rarely trips for the recursive
            // cluster; it remains a backstop for a genuinely unbounded expansion.)
            let headroom = ctx.produced_budget.saturating_sub(ctx.produced_nodes).saturating_add(1);
            ctx.produced_nodes =
                ctx.produced_nodes.saturating_add(produced_node_count(&field_ty, headroom));
            if ctx.produced_nodes > ctx.produced_budget {
                ctx.adt_stack.pop();
                return produced_budget_degraded_leaf();
            }
            // Flattened union view (unchanged, pre-P4 shape).
            fields.push((format!("__v{}_{}", v_idx.as_usize(), field.name), field_ty.clone()));
            // Trust (B3-2c E6): under the FAITHFUL lane, a drop-free-ZST field
            // collapses to the canonical TrustTy::Unit in the PER-VARIANT view —
            // the lockstep mirror of the producer wall's forced Ty::Unit respell,
            // tested on the GROUND-TRUTH rustc type. The flattened `fields` view
            // above keeps the real spelling (the flat lane + every verifier lane
            // are byte-identical; eligible enums never consume the flat view).
            let variant_field_ty = if faithful_scalars()
                && extractor_drop_free_zst(tcx, field.ty(tcx, args).skip_normalization(), ctx)
            {
                TrustTy::Unit
            } else {
                field_ty
            };
            // Per-variant constructor field, named by the field's own name.
            variant_fields.push((field.name.to_string(), variant_field_ty));
        }
        // The variant's discriminant: the concrete tag rustc assigns (honours
        // explicit `= N` discriminants and `#[repr(iN)]`). `val` is a `u128`
        // bit pattern; widen into the `i128` the `VariantDef` stores.
        let discriminant = adt_def.discriminant_for_variant(tcx, v_idx).val as i128;
        variants.push(trust_types::VariantDef {
            name: variant.name.to_string(),
            discriminant,
            fields: variant_fields,
        });
    }

    ctx.adt_stack.pop();

    // Trust: enum-disc-full-native — classify whether a `Discriminant` read on
    // this enum yields a DENSE tag in `[min_disc, max_disc]` (Direct tag
    // encoding), which is the ONLY case where the native -full bridge may
    // soundly `Assume(min_disc <= disc <= max_disc)` over the extracted tag (so
    // `arr[e as usize]` proves). FAIL-CLOSED (`false`) for EVERY other layout:
    //   - `Variants::Multiple { Niche }` — niche-encoded enums (`Option<&T>`,
    //     `Result<bool, ()>`, `Option<NonZeroU8>`): the discriminant read does
    //     NOT recover a clean `0..n` tag, so the `[min,max]` interval over the
    //     declared discriminants is NOT a sound bound on the read value.
    //   - `Variants::Single` / `Variants::Empty` — a single- or zero-variant
    //     enum has no real tag to bound (and a fieldless 1-variant enum's
    //     "discriminant" read is a constant; bounding it buys nothing).
    //   - layout query Err, or `typing_env == None` — we cannot consult the
    //     layout, so we MUST NOT synthesize the fact.
    // NOTE: this flag is ONLY consulted by the native bridge's `Discriminant`
    // read arm; the flattened `fields` (with `__tag`) and `variants` above are
    // UNCHANGED, so `SetDiscriminant` (the WRITE path) still finds `__tag`.
    let disc_index_safe = enum_discriminant_index_safe(tcx, ty, ctx);

    // Construct directly (not via `adt_enum_with_disc_safety`, which re-derives a
    // dedup'd `fields` union): `lower_enum_adt` builds the RICHER flattened view
    // (`__tag` + per-variant `__v{idx}_{name}` fields) the discriminant/
    // projection machinery and `SetDiscriminant` depend on. Keep `fields`
    // verbatim; thread in ONLY the new `disc_index_safe` classification.
    // Trust (B3-1, RFC TRUST_IR_V2): the FAITHFUL-lane first-class-enum marker.
    // `Some` ONLY on the differential's faithful extraction AND for enums
    // ELIGIBLE for the format's EnumDef spelling — mirroring the THIR
    // producer's `register_enum` gates so both sides register structurally
    // EQUAL defs: every variant field a seedable scalar (ints incl.
    // pointer-width / bool / float — the producer's seed_constant set), no
    // compacted field, a DIRECT tag encoding (`disc_index_safe` — the G1/G2
    // fail-close: niche `Option<&T>`, untagged and layout-exotic enums keep
    // the flat spelling), and a mappable repr hint (`repr(i128)` declines,
    // exactly like the producer's `enum_repr_hint`). The hint itself is
    // CARRIED (as `Some(inner)`) because the producer pins it on its EnumDef —
    // omitting it would make structurally-equal enums disagree on
    // `canonical_tag_repr` (a false NotRun). The legacy lane and every
    // ineligible enum get `None` — byte-identical historical behavior.
    let eligible = faithful_scalars()
        && !compacted
        && disc_index_safe
        && !variants.is_empty()
        && variants.iter().all(|v| {
            v.fields.iter().all(|(_, t)| {
                matches!(
                    t,
                    TrustTy::Int { .. }
                        | TrustTy::Bool
                        | TrustTy::Float { .. }
                        | TrustTy::PtrSizedInt { .. }
                        // Trust (B3-2c E6): the canonical drop-free-ZST collapse —
                        // only ever minted by the faithful-lane respell above.
                        | TrustTy::Unit
                )
            })
        });
    let faithful_enum_repr = if eligible { extractor_enum_repr_hint(adt_def) } else { None };
    // Trust (B3-3): the concrete enum layout twin — filled ONLY alongside the
    // faithful first-class spelling (an ineligible enum keeps the flat view,
    // where no trust-ir EnumDef exists to carry a descriptor) and only when
    // the T3 layout gates hold. Decline rules are the LOCKSTEP MIRROR of the
    // THIR producer's `enum_layout_descriptor` fill (trust-thir-lower
    // lib.rs::register_enum): a drifted rule shows up as a descriptor
    // presence/content asymmetry in `tys_agree` (coverage-only Err, never a
    // manufactured divergence), which is the drift tripwire.
    let enum_layout = if eligible
        && !ty.has_non_region_param()
        && !ty.has_non_region_infer()
        && !ty.has_opaque_types()
    {
        ctx.typing_env
            .and_then(|te| tcx.layout_of(te.as_query_input(ty)).ok())
            .and_then(|l| extractor_enum_layout_info(adt_def, &l))
            .map(Box::new)
    } else {
        None
    };
    // Trust: W19 — this arm is reached ONLY for a genuine enum (`lower_enum_adt` is
    // called after the `!is_struct() && !is_union()` guard), so stamp `Enum`. The
    // setter recognizer declines it (an enum is outside the single-anonymous-
    // constructor setter fragment).
    TrustTy::Adt {
        name: name.to_string(),
        fields,
        variants,
        disc_index_safe,
        faithful_enum_repr,
        layout: None,
        enum_layout,
        adt_kind: Some(trust_types::AdtKind::Enum),
    }
}

/// Trust (B3-3): map a rustc enum layout onto the trust-ir-free
/// [`trust_types::EnumLayoutInfo`] twin, or decline (`None`) when the layout
/// is not expressible in the descriptor grammar. Declines (lockstep with the
/// producer fill): `Variants::Empty` (no variant at all), `Variants::Single`
/// over a def that does not declare exactly one variant (the tag-free v37
/// `Untagged` case IS emitted otherwise — see
/// [`extractor_untagged_enum_layout_info`]), and a tag/niche scalar that is
/// not a mappable integer (float or i128; `Pointer` pins to U64 on the 64-bit
/// reference target).
fn extractor_enum_layout_info<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    l: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
) -> Option<trust_types::EnumLayoutInfo> {
    use rustc_abi::{TagEncoding, Variants};
    // Trust (#205R): `Variants::Single` is rustc's verdict that NO discriminant
    // is stored — the enum's image is its sole variant's payload. Handled
    // first, and only for a genuinely one-variant def; everything else about
    // the Single case (no tag lane, no vlayouts) makes the tagged path below
    // inapplicable. LOCKSTEP with the producer's
    // `producer_enum_layout_descriptor`.
    if let Variants::Single { .. } = l.layout.variants() {
        return extractor_untagged_enum_layout_info(adt_def, l);
    }
    let Variants::Multiple { tag, tag_encoding, tag_field, variants: vlayouts } =
        l.layout.variants()
    else {
        return None;
    };
    // Bounds-check BEFORE `FieldsShape::offset`, which PANICS rather than
    // returning an Option — an out-of-range tag_field must decline the
    // descriptor, never abort the compile (lockstep with the producer's
    // `producer_enum_layout_descriptor`).
    if tag_field.as_usize() >= l.layout.fields().count() {
        return None;
    }
    let lane_offset = l.layout.fields().offset(tag_field.as_usize()).bytes();
    let lane_ty = scalar_repr_hint(*tag)?;
    let encoding = match tag_encoding {
        TagEncoding::Direct => trust_types::EnumTagEncodingInfo::Direct {
            tag_offset: lane_offset,
            // Check carrier: the bridge declines the copy-through when this
            // disagrees with the canonical tag repr it computes on the final
            // EnumDef (the descriptor's Direct tag lane is normatively sized
            // at canonical width — a rustc-widened tag must not mint a
            // descriptor whose normative claim is wrong).
            tag_ty: lane_ty,
        },
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            trust_types::EnumTagEncodingInfo::Niche {
                untagged_variant: untagged_variant.as_u32(),
                niche_variants_start: niche_variants.start.as_u32(),
                niche_variants_end: niche_variants.last.as_u32(),
                niche_start: *niche_start,
                niche_offset: lane_offset,
                niche_ty: lane_ty,
            }
        }
    };
    let mut variant_field_offsets = Vec::with_capacity(adt_def.variants().len());
    for (vidx, variant) in adt_def.variants().iter_enumerated() {
        let vl = vlayouts.get(vidx)?;
        // `field_offsets` is DECLARATION-indexed (the memory permutation is a
        // separate private field) — read straight through.
        // `.get()`, not `[]`: a variant layout can carry FEWER offsets than
        // the variant has fields (uninhabited / degenerate variants); an
        // IndexVec index would panic. Decline the whole descriptor.
        let offs: Option<Vec<u64>> = (0..variant.fields.len())
            .map(|i| vl.field_offsets.get(rustc_abi::FieldIdx::from_usize(i)).map(|o| o.bytes()))
            .collect();
        variant_field_offsets.push(offs?);
    }
    Some(trust_types::EnumLayoutInfo {
        encoding,
        size: l.size.bytes(),
        align: l.align.abi.bytes(),
        variant_field_offsets,
    })
}

/// Trust (#205R): the `Variants::Single` half of [`extractor_enum_layout_info`]
/// — a tag-FREE enum image. LOCKSTEP TWIN of the producer's
/// `producer_untagged_enum_layout_descriptor`; the two must decline on exactly
/// the same inputs or every body mentioning such an enum becomes a
/// fill-asymmetry `Err` in `tys_agree`.
///
/// Declines unless the def declares EXACTLY ONE variant. `Variants::Single` is
/// rustc's "no discriminant is stored" verdict, which it also reaches when a
/// multi-variant enum has all but one variant UNINHABITED (`enum E { A(!),
/// B(u8) }` is `Single { index: 1 }`). trust-ir's descriptor still lists every
/// declared variant, and nothing in a tag-free image could pick between them,
/// so its validator/shape/interpreter all reject a multi-variant untagged
/// descriptor — emitting one here would mint a module they refuse.
fn extractor_untagged_enum_layout_info<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    l: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
) -> Option<trust_types::EnumLayoutInfo> {
    let [variant] = &adt_def.variants().raw[..] else {
        return None;
    };
    // With `Variants::Single` the enum layout IS the sole variant's layout, so
    // its own `FieldsShape` carries the payload offsets (there is no per-variant
    // layout list to index). Bounds-check before `offset`, which PANICS.
    let fields = l.layout.fields();
    if variant.fields.len() > fields.count() {
        return None;
    }
    let offsets = (0..variant.fields.len()).map(|i| fields.offset(i).bytes()).collect();
    Some(trust_types::EnumLayoutInfo {
        encoding: trust_types::EnumTagEncodingInfo::Untagged,
        size: l.size.bytes(),
        align: l.align.abi.bytes(),
        variant_field_offsets: vec![offsets],
    })
}

/// The width/signedness hint for a rustc tag/niche scalar: integers map
/// directly, `Pointer` pins to the 64-bit target (U64 — same rule as
/// `IntegerType::Pointer` in `extractor_enum_repr_hint`), floats and i128
/// decline.
fn scalar_repr_hint(s: rustc_abi::Scalar) -> Option<trust_types::EnumReprHint> {
    use rustc_abi::{Integer, Primitive};
    use trust_types::EnumReprHint as R;
    Some(match s.primitive() {
        Primitive::Int(i, signed) => match (i, signed) {
            (Integer::I8, true) => R::I8,
            (Integer::I8, false) => R::U8,
            (Integer::I16, true) => R::I16,
            (Integer::I16, false) => R::U16,
            (Integer::I32, true) => R::I32,
            (Integer::I32, false) => R::U32,
            (Integer::I64, true) => R::I64,
            (Integer::I64, false) => R::U64,
            (Integer::I128, _) => return None,
        },
        Primitive::Pointer(_) => R::U64,
        Primitive::Float(_) => return None,
    })
}

/// Trust (B3-1): the `#[repr]` tag hint for the faithful first-class enum
/// spelling — mirrors the THIR producer's `enum_repr_hint` EXACTLY (pointer-
/// width reprs pin to the 64-bit target; `repr(i128)`/`repr(u128)` decline the
/// whole enum). Outer `None` = ineligible; `Some(inner)` = eligible with the
/// hint's presence/absence carried verbatim.
fn extractor_enum_repr_hint(adt: ty::AdtDef<'_>) -> Option<Option<trust_types::EnumReprHint>> {
    use rustc_abi::{Integer, IntegerType};
    use trust_types::EnumReprHint as R;
    Some(match adt.repr().int {
        None => None,
        Some(IntegerType::Pointer(signed)) => Some(if signed { R::I64 } else { R::U64 }),
        Some(IntegerType::Fixed(i, signed)) => Some(match (i, signed) {
            (Integer::I8, true) => R::I8,
            (Integer::I8, false) => R::U8,
            (Integer::I16, true) => R::I16,
            (Integer::I16, false) => R::U16,
            (Integer::I32, true) => R::I32,
            (Integer::I32, false) => R::U32,
            (Integer::I64, true) => R::I64,
            (Integer::I64, false) => R::U64,
            (Integer::I128, _) => return None,
        }),
    })
}

/// Trust: enum-disc-full-native — `true` iff `ty` is an enum whose layout uses
/// a DIRECT tag encoding over `≥ 2` variants, so its `Discriminant` read yields
/// a dense discriminant the native bridge may bound. FAIL-CLOSED for niche
/// encodings, single/empty layouts, a missing `typing_env`, or a layout error.
/// Trust (B3-2c E6): is this rustc type a DROP-FREE ZST — the extractor mirror of
/// the THIR producer's `is_drop_free_zst` admission predicate. Ground-truth
/// layout test (never the mapped spelling); no typing env / generic / layout
/// Err / drop-bearing all fail closed. Used ONLY under `faithful_scalars()` to
/// collapse a ZST enum-variant field (`()` or a unit struct like `fmt::Error`)
/// to the canonical `TrustTy::Unit` — the same forced respell the producer's
/// `register_enum` wall mints, so both sides' EnumDefs stay structurally equal.
fn extractor_drop_free_zst<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &TyLoweringCtx<'tcx>,
) -> bool {
    let Some(typing_env) = ctx.typing_env else {
        return false;
    };
    if ty.has_non_region_param() {
        return false;
    }
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return false;
    };
    layout.is_zst() && !ty.needs_drop(tcx, typing_env)
}

fn enum_discriminant_index_safe<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    ctx: &TyLoweringCtx<'tcx>,
) -> bool {
    // GATE: must have the body's typing env to query layout. No env ⇒ fail-closed.
    let Some(typing_env) = ctx.typing_env else {
        return false;
    };
    // GATE: a still-generic enum type has no concrete layout. Fail-closed.
    if ty.has_non_region_param() {
        return false;
    }
    // GATE: layout query must succeed. Any Err ⇒ fail-closed.
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return false;
    };
    // GATE-NICHE: Direct tag encoding only. `Niche` (Option<&T>, Result<bool,()>,
    // Option<NonZeroU8>), `Single`, and `Empty` are all fail-closed. Match on a
    // REFERENCE — `LayoutData::variants` is an owned `Variants` reached through a
    // `Deref`, so a by-value `matches!` would try to move out of the layout.
    matches!(&layout.variants, Variants::Multiple { tag_encoding: TagEncoding::Direct, .. })
}

/// Get bit width of an IntTy.
pub(crate) fn int_width_from_int_ty(int_ty: &rustc_ast_ir::IntTy, tcx: TyCtxt<'_>) -> u32 {
    match int_ty {
        rustc_ast_ir::IntTy::Isize => pointer_width(tcx),
        rustc_ast_ir::IntTy::I8 => 8,
        rustc_ast_ir::IntTy::I16 => 16,
        rustc_ast_ir::IntTy::I32 => 32,
        rustc_ast_ir::IntTy::I64 => 64,
        rustc_ast_ir::IntTy::I128 => 128,
    }
}

/// Get bit width of a UintTy.
pub(crate) fn uint_width_from_uint_ty(uint_ty: &rustc_ast_ir::UintTy, tcx: TyCtxt<'_>) -> u32 {
    match uint_ty {
        rustc_ast_ir::UintTy::Usize => pointer_width(tcx),
        rustc_ast_ir::UintTy::U8 => 8,
        rustc_ast_ir::UintTy::U16 => 16,
        rustc_ast_ir::UintTy::U32 => 32,
        rustc_ast_ir::UintTy::U64 => 64,
        rustc_ast_ir::UintTy::U128 => 128,
    }
}

/// Get the pointer width in bits for the target.
fn pointer_width(tcx: TyCtxt<'_>) -> u32 {
    tcx.data_layout.pointer_size().bits() as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug)]
    struct DepthGraphNode {
        adt: bool,
        children: Vec<usize>,
    }

    fn graph_adt_depth(
        graph: &[DepthGraphNode],
        root: usize,
        cutoff: usize,
        node_budget: usize,
    ) -> usize {
        bounded_adt_arg_depth(
            root,
            cutoff,
            node_budget,
            |node| graph[node].adt,
            |node, push| graph[node].children.iter().copied().all(push),
        )
    }

    #[test]
    fn bounded_adt_depth_collapses_a_shared_tuple_dag() {
        let mut graph = vec![DepthGraphNode { adt: true, children: Vec::new() }];
        for previous in 0..1_000 {
            graph.push(DepthGraphNode { adt: false, children: vec![previous, previous] });
        }
        assert_eq!(graph_adt_depth(&graph, 1_000, 5, 4_096), 1);
    }

    #[test]
    fn bounded_adt_depth_clamps_exactly_after_four_adts() {
        let chain = |count: usize| {
            (0..count)
                .map(|index| DepthGraphNode {
                    adt: true,
                    children: (index + 1 < count).then_some(index + 1).into_iter().collect(),
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(graph_adt_depth(&chain(4), 0, 5, 32), 4);
        assert_eq!(graph_adt_depth(&chain(5), 0, 5, 32), 5);
    }

    #[test]
    fn bounded_adt_depth_handles_deep_wrappers_without_recursion() {
        let graph = (0..3_000)
            .map(|index| DepthGraphNode {
                adt: false,
                children: (index + 1 < 3_000).then_some(index + 1).into_iter().collect(),
            })
            .collect::<Vec<_>>();
        assert_eq!(graph_adt_depth(&graph, 0, 5, 4_096), 0);
    }

    #[test]
    fn bounded_adt_depth_wide_or_over_budget_graph_fails_closed() {
        let mut graph = vec![DepthGraphNode { adt: false, children: (1..=4_096).collect() }];
        graph.extend((0..4_096).map(|_| DepthGraphNode { adt: false, children: Vec::new() }));
        assert_eq!(graph_adt_depth(&graph, 0, 5, 4_096), 5);

        let exact = vec![
            DepthGraphNode { adt: false, children: vec![1] },
            DepthGraphNode { adt: false, children: vec![2] },
            DepthGraphNode { adt: false, children: Vec::new() },
        ];
        assert_eq!(graph_adt_depth(&exact, 0, 5, 3), 0);
        assert_eq!(graph_adt_depth(&exact, 0, 5, 2), 5);
    }

    #[test]
    fn bounded_adt_depth_revisits_shared_nodes_at_greater_depth_in_either_order() {
        for root_children in [vec![0, 1], vec![1, 0]] {
            let graph = vec![
                DepthGraphNode { adt: false, children: vec![3] },
                DepthGraphNode { adt: true, children: vec![0] },
                DepthGraphNode { adt: false, children: root_children },
                DepthGraphNode { adt: true, children: Vec::new() },
            ];
            assert_eq!(graph_adt_depth(&graph, 2, 5, 32), 2);
        }
    }

    #[test]
    fn trust_tuple_or_unit_maps_empty_tuple_to_unit() {
        assert_eq!(trust_tuple_or_unit(vec![]), TrustTy::Unit);
    }

    #[test]
    fn trust_tuple_or_unit_preserves_non_empty_tuple() {
        assert_eq!(
            trust_tuple_or_unit(vec![TrustTy::Bool, TrustTy::Int { width: 32, signed: true }]),
            TrustTy::Tuple(vec![TrustTy::Bool, TrustTy::Int { width: 32, signed: true }]),
        );
    }

    #[test]
    fn unsupported_ty_preserves_reason() {
        assert_eq!(
            unsupported_ty("TyKind::Alias", "not normalized"),
            TrustTy::Unsupported {
                kind: "TyKind::Alias".to_string(),
                detail: "not normalized".to_string(),
            },
        );
    }

    #[test]
    fn ty_lowering_context_starts_with_guard_budget() {
        let ctx = TyLoweringCtx::default();

        assert_eq!(ctx.depth, 0);
        assert_eq!(ctx.remaining_nodes, MAX_TYPE_LOWERING_NODES);
        assert_eq!(ctx.produced_nodes, 0);
        assert_eq!(ctx.produced_budget, MAX_TYPE_LOWERING_PRODUCED_NODES);
        assert!(ctx.adt_stack.is_empty());
    }

    /// `produced_node_count` counts EVERY structural node — including each variant
    /// field — short-circuiting at `cap`. This is the produced-tree size the
    /// extraction-time budget charges (the real clone/retain memory cost).
    #[test]
    fn produced_node_count_counts_all_nodes_and_caps() {
        // A leaf is 1 node.
        assert_eq!(produced_node_count(&TrustTy::Bool, 1000), 1);
        // An enum: 1 (Adt) + its flattened `fields` + each variant's fields.
        let enum_ty = TrustTy::adt_enum(
            "E",
            vec![
                trust_types::VariantDef {
                    name: "A".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), TrustTy::Bool), ("1".into(), TrustTy::Bool)],
                },
                trust_types::VariantDef {
                    name: "B".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), TrustTy::Bool)],
                },
            ],
        );
        // adt_enum dedups fields into the union view; count is bounded and > 1.
        let n = produced_node_count(&enum_ty, 10_000);
        assert!(n > 1, "an enum with fields must count more than one node, got {n}");
        // The cap short-circuits: a huge tree costs O(cap).
        let mut fields = Vec::new();
        for i in 0..5_000 {
            fields.push((format!("f{i}"), TrustTy::Bool));
        }
        let fat = TrustTy::adt("Fat", fields);
        assert_eq!(
            produced_node_count(&fat, 100),
            100,
            "counting must short-circuit at the cap (O(cap), not O(size))"
        );
    }

    /// Lever A step 2 — the datatype gate un-degrades EXACTLY `Level` (in the
    /// `clean_kernel` crate, both def-path renderings) and nothing else, so no
    /// other recursive ADT's lowering shifts this step.
    #[test]
    fn is_level_path_matches_only_kernel_level_both_renderings() {
        // Upstream-dependency rendering (crate-name prefixed) and local-crate
        // rendering (no prefix) both match.
        assert!(is_level_path("clean_kernel", "clean_kernel::level::Level"));
        assert!(is_level_path("clean_kernel", "level::Level"));
        // Not Name/Expr, not a same-named type in another crate, not a suffix hit.
        assert!(!is_level_path("clean_kernel", "clean_kernel::name::Name"));
        assert!(!is_level_path("clean_kernel", "clean_kernel::expr::Expr"));
        assert!(!is_level_path("clean_kernel", "clean_kernel::level::LevelArc"));
        assert!(!is_level_path("clean_kernel", "sublevel::Level"));
        assert!(!is_level_path("clean_kernel", "Level"));
        // Right path, WRONG crate — rejected by the crate-name guard.
        assert!(!is_level_path("other_crate", "level::Level"));
        assert!(!is_level_path("other_crate", "clean_kernel::level::Level"));
    }

    /// Lever A step 5 — the `Expr`/`ExprKind` datatype gates un-degrade EXACTLY the
    /// kernel `Expr` struct and `ExprKind` enum (both def-path renderings), and
    /// nothing else — no cross-firing between the two, and no `Level`/`Name`.
    #[test]
    fn is_expr_and_exprkind_paths_match_only_their_target_both_renderings() {
        // Expr struct: both renderings match.
        assert!(is_expr_path("clean_kernel", "clean_kernel::expr::Expr"));
        assert!(is_expr_path("clean_kernel", "expr::Expr"));
        // ExprKind enum: both renderings match.
        assert!(is_exprkind_path("clean_kernel", "clean_kernel::expr::kind::ExprKind"));
        assert!(is_exprkind_path("clean_kernel", "expr::kind::ExprKind"));
        // No cross-firing: the Expr gate must NOT match ExprKind and vice versa.
        assert!(!is_expr_path("clean_kernel", "expr::kind::ExprKind"));
        assert!(!is_expr_path("clean_kernel", "clean_kernel::expr::kind::ExprKind"));
        assert!(!is_exprkind_path("clean_kernel", "expr::Expr"));
        assert!(!is_exprkind_path("clean_kernel", "clean_kernel::expr::Expr"));
        // Neither matches Level/Name, a suffix hit, or a bare name.
        assert!(!is_expr_path("clean_kernel", "clean_kernel::level::Level"));
        assert!(!is_exprkind_path("clean_kernel", "clean_kernel::name::Name"));
        assert!(!is_expr_path("clean_kernel", "other::expr::Expr"));
        assert!(!is_expr_path("clean_kernel", "Expr"));
        assert!(!is_exprkind_path("clean_kernel", "ExprKind"));
        // Right path, WRONG crate — rejected by the crate-name guard.
        assert!(!is_expr_path("other_crate", "expr::Expr"));
        assert!(!is_exprkind_path("other_crate", "expr::kind::ExprKind"));
    }

    /// Lever A step 2 — the transparent-pointer wrapper recognition used to peel a
    /// recursive `Succ(Arc<Level>)` field to a `Level` self-reference. The real
    /// kernel stores children behind `Arc<Level>`; this covers the `Arc`/`Box`/`Rc`
    /// def-path recognition (the fixture exercises the `Ref`/`RawPtr` peel branch).
    #[test]
    fn transparent_pointer_wrappers_recognized_by_def_path() {
        for wrapper in [
            "alloc::sync::Arc",
            "std::sync::Arc",
            "alloc::rc::Rc",
            "std::rc::Rc",
            "alloc::boxed::Box",
            "std::boxed::Box",
        ] {
            assert!(is_transparent_pointer_wrapper(wrapper), "{wrapper} must peel");
        }
        // A non-wrapper nominal ADT (e.g. the kernel `Name`) must NOT peel — its
        // `Param` field stays a by-name datatype reference, not its pointee.
        assert!(!is_transparent_pointer_wrapper("clean_kernel::name::Name"));
        assert!(!is_transparent_pointer_wrapper("clean_kernel::level::Level"));
        assert!(!is_transparent_pointer_wrapper("core::cell::UnsafeCell"));
    }

    /// A by-name recursive datatype reference is a `Ty::Datatype` with the referent
    /// name and an EMPTY variant list — the sort marker a `Level` self-reference /
    /// opaque `Name` field lowers to. SOUNDNESS: it asserts nothing.
    #[test]
    fn recursive_datatype_ref_is_empty_named_datatype() {
        match recursive_datatype_ref("clean_kernel::level::Level") {
            TrustTy::Datatype { name, variants } => {
                assert_eq!(name, "clean_kernel::level::Level");
                assert!(variants.is_empty(), "a by-name reference carries no variants");
            }
            other => panic!("expected an empty-variant Ty::Datatype, got {other:?}"),
        }
    }

    /// The fail-closed degraded leaf is the recursive-ADT `Unsupported` marker
    /// (load-bearing `detail.starts_with("recursive")`) — byte-compatible with the
    /// existing recursive-ADT skip in the consumer. SOUNDNESS: never a provable type.
    #[test]
    fn produced_budget_degraded_leaf_is_recursive_adt_marker() {
        match produced_budget_degraded_leaf() {
            TrustTy::Unsupported { kind, detail } => {
                assert_eq!(kind, "TyKind::Adt");
                assert!(
                    detail.starts_with("recursive"),
                    "leaf must be the fail-closed recursive-ADT marker: {detail}"
                );
            }
            other => panic!("degraded leaf must be the recursive-ADT marker, got {other:?}"),
        }
    }

    // ─── RC-1: canonical recursive-type lowering ────────────────────────────
    //
    // These exercise the two properties the change stands or falls on, WITHOUT a
    // compiler session: (1) the cut set is a function of the type alone, i.e. the
    // greedy FVS restricted to what a root can reach equals the global FVS
    // restricted the same way, for every root and independent of discovery order;
    // (2) a cut point's by-name marker still tells two instantiations of one
    // generic ADT apart.

    /// Successor-closure of `roots` in `edges` — exactly the node set
    /// `canonical_cut_set`'s discovery walk would find from those seeds.
    fn reachable_from(edges: &[Vec<usize>], roots: &[usize]) -> Vec<usize> {
        let mut seen = vec![false; edges.len()];
        let mut work: Vec<usize> = roots.to_vec();
        while let Some(node) = work.pop() {
            if seen[node] {
                continue;
            }
            seen[node] = true;
            work.extend(edges[node].iter().copied());
        }
        (0..edges.len()).filter(|n| seen[*n]).collect()
    }

    /// Induce `edges` on `nodes`, laid out in the given (arbitrary) index order —
    /// the stand-in for a different root's discovery order.
    fn induced_subgraph(edges: &[Vec<usize>], nodes: &[usize]) -> Vec<Vec<usize>> {
        let mut position = vec![usize::MAX; edges.len()];
        for (slot, node) in nodes.iter().enumerate() {
            position[*node] = slot;
        }
        nodes
            .iter()
            .map(|node| {
                let mut succ: Vec<usize> = Vec::new();
                for child in edges[*node].iter().copied() {
                    let slot = position[child];
                    if slot != usize::MAX && !succ.contains(&slot) {
                        succ.push(slot);
                    }
                }
                succ
            })
            .collect()
    }

    /// A `CanonicalCutKey` standing for one type. Only the ordering matters, so
    /// the rendered path carries the whole discriminating weight here.
    fn test_key(name: &str) -> CanonicalCutKey {
        (name.matches("::").count(), name.to_string(), 0, 0)
    }

    fn cut_labels(edges: &[Vec<usize>], names: &[&str], nodes: &[usize]) -> Vec<String> {
        let mut picked: Vec<String> = greedy_feedback_vertex_set(edges, &mut |node| {
            test_key(names[nodes[node]])
        })
        .into_iter()
        .map(|slot| names[nodes[slot]].to_string())
        .collect();
        picked.sort();
        picked
    }

    #[test]
    fn strongly_connected_components_separates_cycle_from_tail() {
        // 0 → 1 → 2 → 0, and 2 → 3 (a tail that never returns).
        let edges = vec![vec![1], vec![2], vec![0, 3], vec![]];
        let alive = vec![true; 4];
        let mut components: Vec<Vec<usize>> = strongly_connected_components(&edges, &alive)
            .into_iter()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        components.sort();
        assert_eq!(components, vec![vec![0, 1, 2], vec![3]]);
    }

    #[test]
    fn strongly_connected_components_skips_dead_nodes() {
        // Same graph with node 1 deleted: the cycle is broken, so every surviving
        // component is a singleton. This is the step the greedy FVS iterates on.
        let edges = vec![vec![1], vec![2], vec![0, 3], vec![]];
        let alive = vec![true, false, true, true];
        let mut components: Vec<Vec<usize>> = strongly_connected_components(&edges, &alive)
            .into_iter()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        components.sort();
        assert_eq!(components, vec![vec![0], vec![2], vec![3]]);
    }

    #[test]
    fn greedy_fvs_leaves_an_acyclic_graph_uncut_and_asks_for_no_keys() {
        // The overwhelmingly common case. It must cost NOTHING beyond one SCC
        // pass — no def-path rendering at all, which is why `canonical_cut_set`
        // computes keys lazily.
        let edges = vec![vec![1, 2], vec![2], vec![3], vec![]];
        let mut key_requests = 0usize;
        let cut = greedy_feedback_vertex_set(&edges, &mut |node| {
            key_requests += 1;
            test_key(&format!("n{node}"))
        });
        assert!(cut.is_empty(), "acyclic graph must have an empty cut set: {cut:?}");
        assert_eq!(key_requests, 0, "an acyclic graph must not render a single def path");
    }

    #[test]
    fn greedy_fvs_cuts_a_self_loop() {
        // `struct S { next: Box<S> }` reduces to a single node with a self edge.
        let edges = vec![vec![0]];
        let cut = greedy_feedback_vertex_set(&edges, &mut |_| test_key("krate::S"));
        assert_eq!(cut, vec![0]);
    }

    #[test]
    fn greedy_fvs_cuts_the_shallowest_def_path_in_the_cycle() {
        // The measured `xor_all` cycle: Tree ↔ Arc ↔ NonNull ↔ ArcInner. The cut
        // must land on `Tree` — the type the cycle is ABOUT — not on an std
        // container internal, so the marker names something the consumer can
        // recognize.
        let names = ["xor_all::Tree", "std::sync::Arc", "std::ptr::NonNull", "alloc::sync::ArcInner"];
        let edges = vec![vec![1], vec![2], vec![3], vec![0]];
        let nodes: Vec<usize> = (0..4).collect();
        assert_eq!(cut_labels(&edges, &names, &nodes), vec!["xor_all::Tree".to_string()]);
    }

    /// THE root-independence property. Every root's discovery finds a
    /// successor-closed subset of the global graph, in its own index order; the
    /// cut it computes must be the global cut restricted to that subset. If this
    /// fails, one rustc type still reaches the dump as two different unrollings —
    /// the defect RC-1 exists to remove.
    #[test]
    fn greedy_fvs_is_root_independent() {
        // Two independent cycles plus an entry node that reaches both, plus a
        // second entry that reaches only one of them, plus a nested cycle so the
        // greedy loop has to iterate.
        //   0 entry_both → 1, 5
        //   1 a::Alpha ↔ 2 zzz::AlphaBox        (cycle A)
        //   3 entry_alpha → 1
        //   5 b::Beta → 6 zzz::BetaMid → 7 zzz::BetaTail → 5, and 6 → 6 (nested)
        let names = [
            "e::EntryBoth",
            "a::Alpha",
            "zzz::AlphaBox",
            "e::EntryAlpha",
            "e::EntryBeta",
            "b::Beta",
            "zzz::BetaMid",
            "zzz::BetaTail",
        ];
        let edges: Vec<Vec<usize>> = vec![
            vec![1, 5], // 0
            vec![2],    // 1
            vec![1],    // 2
            vec![1],    // 3
            vec![5],    // 4
            vec![6],    // 5
            vec![7, 6], // 6
            vec![5],    // 7
        ];

        let all: Vec<usize> = (0..edges.len()).collect();
        let global = cut_labels(&edges, &names, &all);
        assert!(!global.is_empty(), "the fixture must actually contain cycles");

        for root in 0..edges.len() {
            let nodes = reachable_from(&edges, &[root]);
            let reachable_names: Vec<String> =
                nodes.iter().map(|n| names[*n].to_string()).collect();
            let expected: Vec<String> = global
                .iter()
                .filter(|name| reachable_names.contains(name))
                .cloned()
                .collect();

            // Discovery order is whatever order the walk happened to meet the
            // nodes in. Try several, including the reverse, to prove the pick is
            // decided by the key and never by an index.
            let mut orders = vec![nodes.clone()];
            let mut reversed = nodes.clone();
            reversed.reverse();
            orders.push(reversed);
            let mut rotated = nodes.clone();
            rotated.rotate_left(nodes.len() / 2);
            orders.push(rotated);

            for order in orders {
                let sub = induced_subgraph(&edges, &order);
                let actual = cut_labels(&sub, &names, &order);
                assert_eq!(
                    actual, expected,
                    "root {} ({}) with discovery order {:?} computed a different cut set",
                    root, names[root], order
                );
            }
        }
    }

    /// The merge hazard the identity-bearing marker exists to close. A cut point
    /// is emitted with NO structure, so its name is the only thing that separates
    /// two instantiations of one generic ADT. With the generics-erased def path
    /// (the first draft of RC-1) `Foo<u8>` and `Foo<i32>` collapse to one marker
    /// and the consumer's structural comparator reports two genuinely different
    /// types as EQUAL — strictly worse than the non-canonicity it was fixing,
    /// because that direction fails OPEN.
    #[test]
    fn canonical_cut_marker_must_carry_the_instantiation() {
        let erased_u8 = recursive_datatype_ref("krate::Foo");
        let erased_i32 = recursive_datatype_ref("krate::Foo");
        assert!(
            erased_u8.eq_ignoring_disc_index_safe(&erased_i32),
            "the erased-name draft really does merge the two instantiations"
        );

        let instantiated_u8 = recursive_datatype_ref("krate::Foo<u8>");
        let instantiated_i32 = recursive_datatype_ref("krate::Foo<i32>");
        assert!(
            !instantiated_u8.eq_ignoring_disc_index_safe(&instantiated_i32),
            "distinct instantiations of one recursive ADT must not compare equal"
        );

        // …and a cut point with no generic arguments keeps the EXACT legacy
        // marker, so the Lever A `Level`/`Expr`/`ExprKind` cluster and `Tree` are
        // byte-identical to pre-RC-1.
        assert!(
            recursive_datatype_ref("clean_kernel::level::Level")
                .eq_ignoring_disc_index_safe(&recursive_datatype_ref("clean_kernel::level::Level"))
        );
    }

    /// An ordinary (acyclic) lowering must keep using the memo, so
    /// `TyLoweringCtx` starts with an empty cut set — and with NO cut-point
    /// expansion pending, since `expand_cut_point` is set only by
    /// `cut_point_definition` and a walk that started with one set would emit a
    /// definition where a marker belongs.
    #[test]
    fn ty_lowering_context_starts_with_an_empty_canonical_cut() {
        let ctx = TyLoweringCtx::default();
        assert!(ctx.canonical_cut.is_empty());
        assert!(ctx.expand_cut_point.is_none());
    }

    /// R0: the definition table's KEY/VALUE agreement, at the producer end.
    ///
    /// `canonical_cut_ref` keys a generic cut point by its INSTANTIATED def path
    /// while `lower_enum_adt` / `lower_adt_as_datatype` name the definition they
    /// build with the ERASED one. `rename_definition` is what reconciles them;
    /// without it `trust_types::insert_datatype_def` would file `Foo<u8>`'s
    /// definition under `k::Foo` — colliding with `Foo<i32>`'s — and
    /// `trust_types::datatype_definition` would refuse to serve it under the key
    /// the marker actually carries.
    #[test]
    fn a_recorded_definition_is_renamed_to_the_key_its_marker_carries() {
        let variants = vec![(
            "Mk".to_string(),
            vec![("0".to_string(), TrustTy::Int { width: 8, signed: false })],
        )];
        let erased = TrustTy::Datatype { name: "k::Foo".into(), variants: variants.clone() };

        // A generic cut point: the definition is restated under the instantiated
        // key, so it agrees with the marker `canonical_cut_ref` emits.
        let renamed = rename_definition(erased.clone(), "k::Foo<u8>");
        assert_eq!(
            trust_types::definitional_datatype_name(&renamed),
            Some("k::Foo<u8>"),
        );
        let mut defs = trust_types::DatatypeDefs::new();
        assert!(trust_types::insert_datatype_def(&mut defs, renamed));
        assert!(
            trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref("k::Foo<u8>"))
                .is_some(),
            "the marker's own name must find its definition",
        );
        // …and the OTHER instantiation, which is a different cut point, does not
        // pick it up — nor does the generics-erased name `compact_oversized_field`
        // would spell.
        for other in ["k::Foo<i32>", "k::Foo"] {
            assert!(
                trust_types::datatype_marker_definition(&defs, &recursive_datatype_ref(other))
                    .is_none(),
                "`{other}` must not resolve through `k::Foo<u8>`'s entry",
            );
        }

        // A NON-generic cut point keeps the exact erased name: the rename is the
        // identity, so nothing in the Lever A `Level`/`Expr`/`ExprKind` cluster
        // moves.
        assert_eq!(rename_definition(erased.clone(), "k::Foo"), erased);
    }

    /// R0: `compact_oversized_field` must stay UNRESOLVABLE, and the mechanism is
    /// WRITE AUTHORITY, not the shape of the marker.
    ///
    /// For a non-generic type the three producers of `Ty::Datatype { name,
    /// variants: [] }` emit byte-identical markers, so no consumer can tell them
    /// apart by inspection. What separates them is that only
    /// `record_cut_definition` ever writes an entry: a compacted field's marker,
    /// and the `__trust_compacted_aggregate` fallback, therefore resolve to
    /// nothing and every consumer declines on them exactly as before the table
    /// existed.
    #[test]
    fn a_compacted_field_marker_is_never_resolvable_as_a_cut_point() {
        // A big nested aggregate compacts to a marker naming the ADT it replaced…
        let big = TrustTy::Adt {
            name: "k::Big".into(),
            fields: vec![("0".into(), TrustTy::Int { width: 8, signed: false })],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
        };
        let compacted = compact_oversized_field(&big);
        assert_eq!(compacted, recursive_datatype_ref("k::Big"));
        // …and to the fallback name when the field is not a named aggregate.
        assert_eq!(
            compact_oversized_field(&TrustTy::Tuple(vec![TrustTy::Bool])),
            recursive_datatype_ref("__trust_compacted_aggregate"),
        );

        // A table carrying a DIFFERENT cut point resolves neither of them. This is
        // the fail-open the withdrawn by-name body search opened: a compacted
        // `Big<u8>` field binding to a declared `Big<i32>`.
        let mut defs = trust_types::DatatypeDefs::new();
        assert!(trust_types::insert_datatype_def(
            &mut defs,
            rename_definition(
                TrustTy::Datatype {
                    name: "k::Big".into(),
                    variants: vec![(
                        "Mk".to_string(),
                        vec![("0".to_string(), TrustTy::Int { width: 32, signed: true })],
                    )],
                },
                "k::Big<i32>",
            ),
        ));
        for marker in [&compacted, &recursive_datatype_ref("__trust_compacted_aggregate")] {
            assert!(
                trust_types::datatype_marker_definition(&defs, marker).is_none(),
                "a compacted marker must resolve to nothing: it is a SIZE BOUND, \
                 not a back-edge, and binding it would be the withdrawn fail-open",
            );
        }
    }
}

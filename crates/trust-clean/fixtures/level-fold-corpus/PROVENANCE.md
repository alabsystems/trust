# level-fold-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Fourteen real `-Ztrust-dump=mir:<dir>` dumps (never hand-transcribed) of the
**REAL clean-kernel `Level` family** (`first-party/clean/crates/clean-kernel/
src/level/mod.rs`, byte-for-byte vendored by the
`../census-m6-cleankernel-2026-07-08/extract-foldmemo` census crate — see ITS
provenance for the file-level copy audit), compiled by the prebuilt stage2
`trustc` (`rustc 1.99.0-dev (8e74b3bab 2026-07-10) (trustc)` — the fresh
closure-REBUILD binary, whose extractable closure bodies this corpus's P-STACK
rows depend on) in dump-only survey mode. One-command reproduction:
`./regenerate.sh`. The script applies `RUSTFLAGS=-Ztrust-verify=off` to
dependencies, then uses `cargo rustc --lib -- -Ztrust-verify=on
-Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory` so the tracked
dump policy reaches only the selected crate.

This is the RUNG-B **real-code pilot** of the structural-fold lane
(`docs/design/2026-07-10-structural-fold-lane.md` §5 Rung B): the Level ADT
mirror (`TLevel`, 5 constructors: `Zero | Succ(Arc) | Max(Arc,Arc) |
IMax(Arc,Arc) | Param(Name)`) registered from the dump's own type info, with
the first REAL clean-kernel functions any lane certifies self-recursively.
Consumed by `tests/level_fold_corpus.rs` through the production
`prove_dump_dir` pipeline.

## The fourteen members

| dump | role | expected outcome |
|---|---|---|
| `level__Level__is_zero.json` | REAL bool fold: `Zero=>true; Succ(_)\|Param(_)=>false; Max(a,b)=>f(a)&&f(b); IMax(_,b)=>f(b)` | **FULLY_FAITHFUL via trust-ir** (bool lane: cond-tree `&&`, SHARED `Succ\|Param` arm, opaque `Param(Name)` payload, direct self-recursion through the pinned Arc-deref) |
| `level__Level__is_nonzero.json` | REAL bool fold (the `\|\|` dual, shared `Zero\|Param` arm) | **FULLY_FAITHFUL via trust-ir** |
| `level__Level__has_params_impl.json` | REAL bool fold whose recursion routes through `stack_safe(\|\| l.has_params_impl())` closures — the P-STACK debut | **FULLY_FAITHFUL via trust-ir** (each `stack_safe` call fingerprint-resolved: trampoline body + closure body + capture provenance, then the IH slot); with an EMPTY sibling-body map it honestly declines `not_self_recursive` |
| `level__Level__has_params_impl__{closure#0,1,2}.json` | the three recursion closures (Succ / Max\|IMax left / Max\|IMax right) | fingerprint inputs (their OWN rows stay non-FF: 2-call bodies whose callees are outside the registry) |
| `level__Level__has_params.json` | the REAL public wrapper `stack_safe(\|\| self.has_params_impl())` | **FULLY_FAITHFUL via trust-ir** (the rung-B WRAPPER arm: wrapper fingerprint + the inner fold's witness re-run; P-STACK premise) |
| `level__Level__has_params__{closure#0}.json` | the wrapper's delegation closure | fingerprint input |
| `expr__stack_safe.json` | clean-kernel's REAL `stack_safe` (generic dump: the exact two-literal `stacker::maybe_grow(32768, 1048576, f)` forwarding call) | the P-STACK fingerprint target; its own row is out of every lane (generic `Unsupported` locals) |
| `level__Level__substitute_map.json` | REAL wrapper `stack_safe(\|\| self.substitute_map_impl(subst))` — TWO captures | decline `stack_safe_drift` as a wrapper (captures ≠ exactly the param), `non_int_return` as a fold — honestly blocked |
| `level__Level__substitute_map_impl.json` | `impl_opt.unwrap_or_else(clone)` | decline `non_int_return` (ADT-valued) |
| `level__Level__substitute_map_impl_opt.json` | the E-sort-blocking recursive fold (`Option<Level>`-valued) | decline `non_int_return` — the honest rung-B blocker row (see below) |
| `level__Level__substitute_slice_impl_opt.json` | same family, slice-keyed | decline `non_int_return` |
| `level__Level__collect_params_impl.json` | REAL accumulator-SHAPED traversal with TWO accumulators (`&mut Vec<Name>` + `&mut HashSet<Name>`) whose `insert` bool GUARDS the push | decline `param_shape_unsupported` (multi-accumulator; even under a 2-acc model its insert-bool read is design-§4-rule-(ii) `accumulator_read`) |

## Why the `substitute_map`/`substitute_slice` family is honestly out of rung-B reach

Read off these dumps (the mission's E-sort question — `LevelParamSubst{,Slice}::
fold_sort_opt`'s blocked callees):

1. **ADT value domain**: return type `Option<Level>` — the OptE domain debuts
   at rung C per the design (§5); rung B's sorts are Int/Bool/Acc.
2. **Smart-constructor rebuilds**: the changed-children rebuild calls
   `Level::max` / `Level::imax` (3 call sites each in the dump) — NOT free
   constructor applications (`max` runs `is_geq` subsumption; `imax` reduces
   to `max`/`Zero`/…). Even rung C's free-ctor OptE rebuild cannot express
   them; they need ADT-valued certified-callee denotations (design §3.4 — the
   rung-E transport), and `Level::max`/`is_geq` are themselves recursive +
   `hashbrown`-memoized.
3. **Map lookup**: `HashMap::<K,V,S,A>::get` on the substitution (would need
   an uninterpreted-total-key model — the `idxElem` tier — for a *read*
   accumulator, a lane that does not exist yet).
4. **Higher-order combinators**: `Option::map` / `Option::and_then` with
   closure arguments.
5. **`__trust_total_clone`** ×4 (the P-CLONE premise tier, design §2).

The recursion's `stack_safe` routing (item 7 of the module doc) is NOT on this
list — rung B's P-STACK machinery handles it (proven by `has_params_impl`).
Consequently the judge E-sort rows stay blocked at rung B **twice over**: their
callees don't certify, AND the call-lane transport (`CalleeFact`: arity +
requires only, `callResult : Int`) could not consume an ADT-valued fold
certificate even if they did (design §3.4 = rung E). Expected judge-66 delta
from rung B: **0** — the honest outcome the design's rung ladder predicts.

## MIR facts the recognizer is pinned against (read off these real dumps)

* `level::Level` is **niche-encoded** (`disc_index_safe: false`; `Param(Name)`
  is the untagged variant — confirmed via `-Zprint-type-sizes` probes on the
  realistic shape), yet the entry `SwitchInt(Discriminant((*_1)))` carries the
  LOGICAL tags 0..=4 with `exhaustive_enum_unreachable: true`. That flag is
  stamped by extraction ONLY when the case set equals
  `adt_def.discriminants(tcx)` — layout-independent — which is what makes the
  rung-A `disc_index_safe` gate unnecessary for the tag→variant map (module
  doc item 8 of `src/trustir_fold.rs`).
* `Succ(_) | Param(_) => false` dumps as TWO switch targets sharing ONE arm
  block; `Max(l1,l2) | IMax(l1,l2) => …` (in `has_params_impl`) dumps as two
  variant-specific Downcast prefixes converging on a shared body block — the
  per-variant walk handles both; a shared arm touching variant fields would
  still decline for the mismatched variant (Downcast-exact projection check).
* The `ArcInner` def-path in this extract renders as
  `smallvec::alloc::sync::ArcInner` (crate-prefixed re-export) — the
  P-ARC-DEREF pin accepts exactly the `alloc::sync::ArcInner` suffix.
* `stack_safe`'s dump is GENERIC (locals are `Unsupported: TyKind::Param`) —
  one dump serves all instantiations; the fingerprint checks the call
  structure (`stacker::maybe_grow(32768, 1048576, Copy(_1))` → `Return`),
  which is fully monomorphization-independent.
* The recursion closures capture exactly one `&Arc<Level>` field ref; their
  bodies are `deref-then-call` (3 blocks); the wrapper closure captures the
  `&Level` param and is `direct-call` (2 blocks).

## Honesty notes

* Premises carried by the FF rows here (module doc of `src/trustir_fold.rs`):
  P-ACYC, P-ARC-DEREF, and — new at rung B — P-STACK
  (`stacker::maybe_grow(r,s,f) = f()`; third-party FFI via psm, permanently
  uncertifiable in-pipeline, quarantined by the exact-shape fingerprint).
* The witness is MODEL-ONLY (the `trustir_adt.rs` tier): kernel-checked,
  self-contained, not grounder-connected.
* `Param(Name)`'s payload is an OPAQUE atom in the model (design §1); the
  certified folds provably never read it (any read is the named decline
  `opaque_payload_read`).
* ZFC-nesting validation item (design §5 rung B): **Level is a single,
  non-mutual inductive** — no 2-block mutual registration is needed at Level
  scale, so the mutual/nested-block validation genuinely defers to Expr scale
  (`ZFCSetExpr`), where the real 2-type SCC (`Expr::has_loose_bvar_in_range`
  ↔ `ZFCSetExpr::has_loose_bvar_in_range`) lives.

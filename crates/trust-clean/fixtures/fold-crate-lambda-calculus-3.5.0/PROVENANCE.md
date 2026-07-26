# fold-crate-lambda-calculus-3.5.0 — the structural-fold lane's FIRST published-crate intake (2026-07-11)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

**Status: RUNG G LANDED (2026-07-12) — P-BOX-DEREF + G2 + G3; first
published-crate self-recursive KERNEL WITNESS minted.** The 2026-07-11 intake
below measured the gap queue; rung G (`src/trustir_fold.rs` module doc items
9–10) landed G1a (the `Box → Unique → NonNull → RawPtr` sibling type walk),
G1b (the two-block inline ub-check fingerprint, both asserts
premise-discharged under P-BOX-DEREF, drift → the NAMED `box_deref_drift`),
G2 (boxed-pair per-component IH slots), and G3 (the threaded `depth`
parameter: motive `Int → σ`, `ih (d+1)` at the binder). Measured result on
this corpus (census: `census/` refreshed + the rung-G before/after fixture):

* `term::Term::has_free_variables_helper` — the intake's named first target
  (Bool sort, ZERO foreign callees) — RECOGNIZES (`fold_shape_ok`) and its
  kernel witness MINTS modulo 3: recursor-defined-total interpreter over
  `Term { Var(Int), Abs(T), App(T, T) }` (App's two slots from ONE boxed
  pair) + per-variant adequacy. Exactly as §5's honesty note predicted, it
  stays HONESTLY short of FULLY_FAITHFUL at the ONE measured gated residue:
  the Abs arm's `depth + 1` Add-overflow VC (genuinely satisfiable over an
  unbounded depth; per-VC trace: 3 fingerprint `align−1` Sub VCs refute
  trivially, the Add does not). NOT forced — the overflow story
  (bounded-depth premise / checked-arith rewrite) remains named future work.
* `term::Term::max_depth` — the former `opaque_payload_read` headline — now
  walks THROUGH both Box arms and declines at the NEXT named gate:
  `foreign_value_in_arm` on `std::cmp::Ord::max` (the G4 queue). Likewise
  `max_free_index_helper` → `foreign_value_in_arm` on `saturating_sub`.
* Box-specific FORGERIES (doctored fingerprint blocks, swapped ub-check
  asserts, non-Box/non-Unique walks, swapped-pair claimed RHS) decline
  `box_deref_drift` / KernelReject — pinned in
  `tests/fold_crate_lambda_calculus.rs`.
* `kernel_rejected = 0`; zero collateral on every other corpus (before/after
  ff-gate TSVs byte-identical); staging-66 / judge-59 aggregates unchanged.

The original intake record (§1–§6, kept verbatim below) documents the
2026-07-11 BLOCKED-named state this rung flipped.

**Original status (2026-07-11): BLOCKED-named — `box_deref` (P-BOX-DEREF).**
The fold lane (rungs A–E) certifies self-recursive folds over `Arc`-recursive
enums; the 2026-07-11 crate-ladder re-census
(`reports/crate-ladder-recensus-2026-07-11.md`) proved the nine existing
published-crate corpora contain ZERO self-recursion, so the lane had never
been pointed at a published crate. This corpus is that intake: a real
crates.io crate whose core IS recursive-ADT traversal, dumped and scored
through the production gates AS-IS. Result: a real 18-function recursion
population, zero immediate certificates, and a NAMED, measured gap queue
(§4–§5) — the rung-G work list. No recognizer/pipeline source was touched;
fail-closed behavior is exactly what this corpus pinned at intake
(`tests/fold_crate_lambda_calculus.rs`).

## 1. Crate provenance (real, published, byte-verified)

| field | value |
|---|---|
| crate | `lambda_calculus` |
| version | `3.5.0` (latest; not yanked; published 2026-06-30) |
| source | `https://static.crates.io/crates/lambda_calculus/lambda_calculus-3.5.0.crate` |
| sha256 (verified against the crates.io API `version.checksum` field, 2026-07-11) | `168030aef659e9a35ba517952982bb0212fda53d531837e3f18c399f9d28dba8` |
| downloads | 67,340 all-versions (crates.io API, 2026-07-11) |
| edition | 2024 (published Cargo.toml; `rust-version = "1.88"`) |
| dependencies | **zero** |
| unsafe | `#![deny(unsafe_code)]` (crate root) |
| repository | <https://github.com/ljedrz/lambda_calculus> |
| license | CC0-1.0 |
| description | "A simple, zero-dependency implementation of pure lambda calculus in Safe Rust" |

`SOURCE/` is the **verbatim** tarball extract — byte-identical to the
published `.crate` (re-check with `./regenerate.sh --verify-source
--output-root <new-scratch-path>`: download, sha256 pin check, `diff -r`).
`metadata/source-selection.json` is the machine-readable local pin: it binds the crate,
version, archive checksum, Cargo default-feature selection, publisher VCS
commit, and a canonical manifest of all 46 vendored files. Nothing was
hand-transcribed, flattened, or edited. The recursive ADT at the crate's heart
(`SOURCE/src/term.rs`):

```rust
pub enum Term {
    Var(usize),
    Abs(Box<Term>),
    App(Box<(Term, Term)>),
}
```

Candidate evaluation that selected this crate (dump-ability × fold-shape
match): `binary_search_tree` 0.2.2 is a generic `T: Ord` struct-node tree
behind `Option<Box<Node>>`, `avl` 0.7.1 is generic struct nodes linked by raw
`NonNull` parent/child pointers, `splay-safe-rs` 0.8.3 carries 3 deps
(compare/num-traits/serde) — for all three the declines would be
uninformative "not an enum / not self-recursive" noise; `rose_tree` is
petgraph-arena-backed (no recursion at all),
`minilamb` 0.1.1 has `App(Vec<Expr>)` container children, `math-ast` 0.2.0 /
`lamb` 0.1.0 are payload-generic, tiny calculator crates (`rzcalc`, `wcal`,
`math-calc`, `rcalc`) are lifetime-generic/struct-node/token-stream, and
serde_json::Value helpers recurse through `Vec`/`Map` containers AND need
serde_json as an extern (not standalone-dumpable). `lambda_calculus` is the
unique candidate that is concrete, zero-dep, safe, tiny, AND genuinely
fold-shaped — its only distance from the lane is exactly the pointer-type
premise (Box vs Arc), which is the question this intake exists to measure.

## 2. Dump recipe + committed scope

Real `TRUST_DUMP_MIR` dumps (never hand-transcribed) by the prebuilt stage2
`rustc 1.99.0-dev (8e74b3bab 2026-07-10) (trustc)` — the census-m6 recipe
(`-Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory`), at the
crate's own edition and default feature set
(`--edition 2024 --cfg 'feature="encoding"' --crate-type lib`). Non-destructive
reproduction requires a new output directory and an exact repository-local
Stage2 compiler:

```console
./regenerate.sh \
  --trustc ../../../../build/<host>/stage2/bin/trustc \
  --output-root /absolute/new/scratch/path
```

That writes `full/`, the mechanically selected `core/`, the exact compiler
argv, stdout/stderr, exit status, and counts under the scratch path. It does not
edit this fixture. Replacing the checked-in core dumps requires the separate,
explicit `--replace-committed` spelling. Ambient `TRUSTC` and ambiguous
auto-selection are rejected.

From the repository root, collect an exact-HEAD diagnostic receipt over this
one crate (Python 3.11 or newer is required):

```console
python3 scripts/collect_lambda_calculus_diagnostic.py \
  --stage2-root build/<host>/stage2 \
  --output build/evidence/lambda-calculus-3.5.0-diagnostic.json
```

The collector requires a clean recursive Git checkout and accepted Stage2
provenance; binds exact sibling `trustc`, `targo`, `targo-trust`, and `trustd`
identities/hashes; independently downloads the fixed HTTPS `.crate`, records the
fixed-path curl hash and bounded fetch transcript, enforces the collector-owned
SHA-256 pin, parses the archive without extracting it, and requires its complete
regular-file path/size/hash manifest to equal `SOURCE/`. A pre-downloaded archive
may be supplied with `--source-archive`; that changes only acquisition, never the
collector-owned URL/checksum or exact-file comparison. Both the archive and
vendored tree are checked again after measurement. Thus editing `SOURCE/` and
its adjacent selection manifest together cannot preserve the published-source
claim. The collector then generates new full/core dumps without touching these
tracked dumps and runs `targo trust prove --format=json` over the core selection
with an explicit budget. It rejects internally inconsistent scorecards (including
fully-faithful witness partitions, proven/declined overlap, and safety-subtype
overcounts) and atomically publishes only a complete accepted receipt, so a
failed rerun leaves a prior receipt unchanged. The result is deliberately labelled
a **one-published-crate, non-representative diagnostic**. It is not an ecosystem
sample, Cargo compatibility evidence, full-crate proof coverage, or a superiority
result.

The full crate dumps **291** functions. Committed here: the **90 dumps of the
hand-written algorithmic core** — everything except the `data` module (the
mechanical Church/Scott/Parigot encoding zoo: ~200 Term-BUILDER dumps, ~58 MB,
and — measured on the full 291 before scoping — **zero** self-recursive
functions among them). The scope rule is mechanical (`*data__*` filenames
excluded, see regenerate.sh) and loses no recursion: all 18 direct-self-
recursive functions in the entire crate live in the committed core
(term/reduction/parser modules). The scope is also COMPOSITION-CLOSED:
no committed function has a callee in the dropped module (measured off the
dumps' own call terminators — `data::` callees: NONE), so every verdict over
the 90 is identical to its verdict inside the full 291. The full-crate dump
remains one edit away.

The collector records `runner_execution_authenticated: false` and
`release_gate_admissible: false`: Python startup authority is ambient before
the script can scrub it. This JSON is bounded diagnostic evidence only, never
release-gate proof.

## 3. The recursion population — what the ladder never had

Of the 90 core dumps, **18 are direct-self-recursive** (first committed
published-crate corpus with ANY): 

| family | functions | shape |
|---|---|---|
| pure Term folds | `Term::max_depth` | `&Term -> u32`, 1 param — **the lane-shaped candidate** |
| parameterized Term folds | `Term::has_free_variables_helper`, `Term::max_free_index_helper` | `(&Term, usize) -> bool/usize` — depth threaded |
| binary Term fold | `Term::is_isomorphic_to` | `(&Term, &Term) -> bool` |
| mutating reducers | `beta_{nor,cbn,cbv,app,hap,hno,hsp}`, `_apply`, `update_free_variables` | `(&mut Term, …) -> ()`, 3 params |
| display recursion | `show_precedence_cla`, `show_precedence_dbr` | `-> String` |
| slice recursion (not ADT) | `parser::{_convert_classic_tokens, _get_ast, fold_exprs}` | recurse over `&[(C)Token]` |

## 4. Production-gate verdicts AS-IS (measured 2026-07-11, this tree)

Instruments (all census-only, additive; built from this tree,
`RUSTC_BOOTSTRAP=1`, debug):

* `src/bin/fold-crate-intake-2026-07-11.rs` — per-function fold-lane triage
  through the real `sem_structural_fold_shape_of_with_bodies` entry point
  (sibling bodies threaded, as production);
* `src/bin/ff-gate-diagnose-2026-07-10.rs` — the production-pinned
  FULLY_FAITHFUL gate, per row, callees-first, NO budget (verdicts
  definitive, never timeout artifacts);
* `src/bin/census-2026-07-06.rs --aggregate` — one
  `prove_dump_dir_with_budget_and_bodies` pass (what `targo trust prove`
  drives), `TRUST_CENSUS_BUDGET_SECS=60`. Still in flight at commit time
  (~18 recursion-family functions each burn the full 60 s budget); its
  interim behavior is already the honest production story — fail-closed
  `⏱ DECLINED (per-function budget exceeded)` on the recursion family
  (`max_depth`, `max_free_index_helper`, `show_precedence_cla`,
  `_convert_classic_tokens`, …), zero proofs minted, consistent with the
  definitive UNBUDGETED ff-gate verdicts above. One-command reproduction:
  the ff-gate.tsv def_path column as `--targets-file`.

Evidence TSVs: `census/` in this directory. The per-row FF verdicts cited
here are the ff-gate ones (no budget — definitive, never timeout artifacts).

**Headline: FULLY_FAITHFUL 0 / 90; fold lane `fold_shape_ok` 0 / 90;
kernel_rejected 0. FF-gate clusters: 89 SHAPE_GAP + 1 SAFETY_GAP
(`parser::fold_exprs` — mirsem loop shape recognized, safety conjunct open).
The first published-crate self-recursive certificate did NOT mint — the lane
is blocked at named, actionable gates (below), NOT at a mystery.**

Fold-lane triage of the 18-function recursion population, BY NAME:

| decline | rows | what it names |
|---|---|---|
| `opaque_payload_read` ("borrow of opaque field 0 of term::Term::variant#1") | 1 — **`Term::max_depth`** | THE Box gap: signature admitted, enum modeled, entry `SwitchInt(Discriminant)` + `exhaustive_enum_unreachable` accepted, Var arm walkable — and the Abs arm's `&((*_1) as Abs).0` touches a `Box<Term>` field the Arc-pinned classifier calls opaque. G1 below. |
| `non_int_return` | 8 recursive rows | 2-param helpers (`has_free_variables_helper`, `max_free_index_helper` — the FOLD-PARAMETER gap, G3), the binary fold (`is_isomorphic_to`), String/Result returns (`show_precedence_*` ×2, parser fns ×3) |
| `param_shape_unsupported` ("Unit-returning traversal with 3 params…") | 9 recursive rows | the `&mut Term` reduction engines — genuinely outside the pure-fold story (they mutate the tree in place) |
| non-recursive rows | 58 `non_int_return` + 6 `not_self_recursive` + 8 `param_shape_unsupported` | accessors/constructors/Display impls — not fold candidates (whole-corpus totals: 66/6/17 + the 1 `opaque_payload_read`) |

## 5. The measured P-BOX-DEREF gap + extension sketch (rung-G queue)

What the lane pins today (P-ARC-DEREF, `src/trustir_fold.rs`): recursive
child fields must be `std::sync::Arc<enum>` (type walk `Arc → ptr:NonNull →
pointer:RawPtr → ArcInner → data`), and the subterm handle must come from a
pinned `Call` to `std::ops::Deref::deref` (`&Arc<enum> → &enum`).

What this REAL published dump carries instead (read off
`term__Term__max_depth.json`; ub-checks ON, as this toolchain dumps):

* **Type walk (G1a)** — `Abs.0: std::boxed::Box → "0": std::ptr::Unique →
  "pointer": std::ptr::NonNull → RawPtr → Datatype(term::Term)`. A
  `box_pointee_ty` SIBLING of `arc_pointee_ty` (never a relaxation of it —
  pinned by `tests/fold_crate_lambda_calculus.rs::box_field_lowering_chain`).
* **Inline deref fingerprint (G1b)** — Box deref is BUILT-IN, so there is no
  callee to pin; the caller body materializes, per child access: copy the Box
  value out of the field ref; project `.0.0` (Box→Unique→NonNull); cast to
  `*const Term`; an ALIGNMENT ub-check block (`addr & (align-1) == 0` →
  `Assert(MisalignedPointerDereference)`); a NULL ub-check block
  (`!(addr == 0 & true)` → `Assert(Custom "null reference constructed")`);
  then `&(*raw)` and the recursive `Call`. A P-BOX-DEREF premise must
  fingerprint this whole 3-block idiom fail-closed and carry the two
  ub-check asserts as premise-discharged (they ARE Box's validity
  invariant: aligned + non-null), exactly the way P-ARC-DEREF carries
  `Deref::deref`'s contract.
* **Boxed-tuple children (G2)** — `App.0: Box<(Term, Term)>`: ONE field, TWO
  recursive components, reached as `&((*raw).0)` / `&((*raw).1)`. The
  `FoldFieldKind::Recursive` model is per-FIELD (one IH slot); tuple-in-box
  needs per-COMPONENT slots (recursor minor-premise arity changes — a model +
  registration extension, not just a walker one).
* **Fold parameters (G3)** — `has_free_variables_helper(&self, depth)` /
  `max_free_index_helper(&self, depth)`: an extra scalar parameter threaded
  through recursion (`depth`, `depth + 1` at Abs). The rung-B accumulator is
  the Unit-returning cousin; value-sorted folds need the motive `Int → σ`.
* **Pinned pure std callees in arms (G4)** — `std::cmp::Ord::max` (both
  `max_depth` and `max_free_index_helper` combine IHs with it) and
  `core::num::<impl usize>::saturating_sub` (Var arm) — foreign-poison today;
  each needs a HASHSET_INSERT-style pinned model.
* **Honesty note — the overflow residue is NOT part of the queue.** Even
  after G1–G4, `max_depth` (`+ 1` at Abs) and both helpers (`depth + 1`)
  carry a `CheckedBinaryOp(Add)` whose overflow VC over an unbounded
  recursive result/parameter is genuinely satisfiable — the same measured
  residue as the authored corpus's `size`/`sum` members. `has_free_variables_
  helper` (zero foreign callees, Bool sort, rung-B `||` cond-tree vocabulary)
  is the closest post-G1/G2/G3 FF candidate, and its Abs arm's `depth + 1`
  still holds it at the safety gate honestly. On THIS crate, a first
  fold-lane FF additionally requires the overflow story (bounded-depth
  premise / checked-arith rewrite) — stated plainly rather than engineered
  around. G1–G4 remain necessary and are the reusable capability; crates
  whose folds combine with overflow-free ops (`^`, `|`, `&`, comparisons,
  `max` alone) would mint immediately once G1(+G2) land.

## 6. Census discipline

* Zero collateral: nothing outside this new directory + the two new additive
  files (`src/bin/fold-crate-intake-2026-07-11.rs`,
  `tests/fold_crate_lambda_calculus.rs`) was touched; no recognizer/pipeline
  source changed, so all prior corpus verdicts are byte-identical by
  construction.
* `kernel_rejected = 0` in every run — no soundness event.
* The BLOCKED state is PINNED: `tests/fold_crate_lambda_calculus.rs` asserts
  the 90/18 population, `max_depth`'s exact `opaque_payload_read` decline,
  the per-class signature declines, and the full Box lowering chain. When
  rung G lands, those pins flip deliberately, one named row at a time.

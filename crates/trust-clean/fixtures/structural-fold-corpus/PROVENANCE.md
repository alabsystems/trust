# structural-fold-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Sixteen real `-Ztrust-dump=mir:<dir>` dumps (never hand-transcribed) of `SOURCE.rs` in
this directory, compiled by the prebuilt stage2 `trustc` in dump-only survey
mode with direct tracked flags (`-Ztrust-dump=mir-only:<dir>
-Ztrust-policy=advisory`, `--edition 2021 --crate-type lib`). One-command
reproduction: `./regenerate.sh`; it contains that direct `trustc` invocation
and uses no ambient verification-policy controls.

Rung-A members were dumped with the pre-REBUILD stage2 binary; the WHOLE
corpus (including all rung-A members) was regenerated 2026-07-10 with the
fresh `rustc 1.99.0-dev (8e74b3bab 2026-07-10) (trustc)` — the rung-A verdicts
are unchanged under the new binary (pinned by `tests/structural_fold_corpus.rs`).

This is RUNGS A + B of the structural-fold lane
(`docs/design/2026-07-10-structural-fold-lane.md` §5 Rungs A-B, §4): the
mini-ADT pilot for the structural-recursion certification story —
recursor-defined-total interpreter + IH-slot mapping + strict-subterm
provenance — extended at rung B with the Bool result sort (cond-tree arms) and
the accumulator lane (motive `Acc → Acc`, opaque `insertAcc`, exact
program-order sequence). Consumed by `tests/structural_fold_corpus.rs` through
the real production `prove_dump_dir` pipeline. (The rung-B REAL-code members —
clean-kernel's `Level` family — live in `../level-fold-corpus/`.)

## The sixteen members

| dump | role | expected outcome |
|---|---|---|
| `xor_all.json` | good fold: `Leaf(v)=>v; One(a)=>f(a); Two(a,b)=>f(a)^f(b)` | **FULLY_FAITHFUL via trust-ir** (BitXor raises no overflow VC) |
| `first_leaf.json` | good fold: payload/IH selection; `Two` IGNORES its second subtree | **FULLY_FAITHFUL via trust-ir** (unused recursive field still gets an IH slot in the model) |
| `tag_xor.json` | good fold over `#[repr(i64)] TaggedTree` (discriminants 10/20/30) | **FULLY_FAITHFUL via trust-ir**; pins "never assume tag == declaration index" — the `SwitchInt` tags are 10/20/30 while the `Downcast` projections are 0/1/2 |
| `size.json` | design-literal member: `1 + f(a) + f(b)` (`CheckedBinaryOp(Add)` + overflow `Assert` in the dumped MIR) | shape-recognized, kernel witness MINTS, **held at the safety gate** — the i64 `ArithmeticOverflow` VC over an unbounded recursive result is genuinely satisfiable (a measured residue of the design, not a recognizer gap) |
| `sum.json` | design-literal member: `Leaf(v)=>v; One(a)=>f(a); Two(a,b)=>f(a)+f(b)` | same as `size` — recognized + witness mints, held at the safety gate |
| `bad_self.json` | adversarial: the `One` arm recurses on the SCRUTINEE (`f(x)=f(x)`) | **decline `non_subterm_recursive_arg`** (detail: scrutinee) |
| `bad_rebuilt.json` | adversarial: recurses on `&Tree::One(a.clone())` — a reconstructed node (the `beta_normalize` shape) | **decline `non_subterm_recursive_arg`** (detail: locally-rebuilt node) |
| `bad_nonsub.json` | adversarial: recurses on `pick(a)` — a sibling-call result | **decline `non_subterm_recursive_arg`** (detail: foreign-call result `pick`) |
| `pick.json` | the foreign sibling callee (`&Tree -> &Tree` identity) | out of lane (`non_int_return`); certifies via the pre-existing straight-line lane |
| `has_leaf_zero.json` | RUNG B bool fold: `Leaf(v)=>v==0; One(a)=>f(a); Two(a,b)=>f(a)\|\|f(b)` | **FULLY_FAITHFUL via trust-ir** (Bool sort; `\|\|` reconstructed as the cond-tree `if f(a) { true } else { f(b) }`; `==` as an `Int.beq` Bool leaf) |
| `all_leaves_pos.json` | RUNG B bool fold (`&&` + `>` comparison) | **FULLY_FAITHFUL via trust-ir** (`if f(a) { f(b) } else { false }`; `>` as the swapped-operand `decide Int.lt` leaf) |
| `collect_leaves.json` | RUNG B accumulator fold (design §4): `&mut HashSet<i64>` threaded unchanged, insert bool discarded | **FULLY_FAITHFUL via trust-ir** (motive `Acc → Acc`, opaque `insertAcc`, the exact post-order sequence `Two(a,b) ⇒ f(b, f(a, acc))`) |
| `sink.json` | the foreign callee the escape adversary feeds | out of lane (`non_int_return`); not fully faithful anywhere |
| `bad_acc_escape.json` | adversarial (§4 rule iii): `sink(out)` — the accumulator (as a shared re-borrow `&(*out)`) reaches a foreign callee | **decline `accumulator_escape`** (detail names `sink`) |
| `bad_acc_read.json` | adversarial (§4 rule ii): `if out.insert(*v) { … }` — insert's bool CONSUMED | **decline `accumulator_read`** (the global never-read set is the fail-closed witness) |
| `bad_acc_alias.json` | adversarial (§4 rule i): the `One` arm recurses with a FRESH `HashSet` (`&mut other`) | **decline `accumulator_alias`** |

## MIR facts the recognizer is pinned against (read off these real dumps)

* The 3-variant match dumps as ONE `SwitchInt(Discriminant((*_1)))` with all
  three variants as EXPLICIT targets, `otherwise` → a bare `Unreachable`
  block, and the TyCtxt-vetted `exhaustive_enum_unreachable: true` flag.
* Both enums here happen to carry `disc_index_safe: true` (Direct tag
  encoding), but rung B REPLACED that gate: the tag→variant map's soundness
  anchor is the `exhaustive_enum_unreachable` flag itself, which extraction
  stamps only when the case set equals the enum's LOGICAL discriminant set
  (`adt_def.discriminants`) — layout-independent, validated on the REAL
  niche-encoded `level::Level` dumps (`../level-fold-corpus/PROVENANCE.md`).
* RUNG B — the bool short-circuits dump as `SwitchInt` on a Bool-typed local
  with targets exactly `[(0, else_bb)]` + `otherwise = then_bb`; the
  comparison leaves as `Rvalue::BinaryOp(Eq/Gt, …)` writing a Bool local.
* RUNG B — the accumulator (`_2: &mut HashSet<i64>`) is passed by plain
  `Copy(_2)` to both `HashSet::<T, S, A>::insert` and the recursive calls
  (optimized MIR copy-propagates the reborrows); `bad_acc_escape`'s escape is
  a `&(*_2)` shared re-borrow; `bad_acc_alias` builds `HashSet::<T>::new()` +
  `&mut _8` and carries a `Drop`/`Resume` unwind pair (the read-set collector
  models `Resume` as read-free — it is the unwind re-raise sink).
* The `Arc` payload deref is a real `Call` to `std::ops::Deref::deref` whose
  argument is the `&((*_1) as Variant).field` borrow and whose destination's
  declared type is `&Tree` — the pinned P-ARC-DEREF idiom (argument type
  `&std::sync::Arc<..>` whose pointee, through the
  `ptr → NonNull → pointer → RawPtr → ArcInner → data` field path in the
  dump's own type info, names the folded enum).
* `+` compiles to `CheckedBinaryOp(Add)` + `Assert(!overflow_flag)` (this
  toolchain dumps with overflow checks on); the recognizer admits the Assert
  on the happy path and the value model reads the pair's `.0` — the overflow
  OBLIGATION stays with the safety pillar, which is exactly what holds
  `size`/`sum` short of FULLY_FAITHFUL.
* `bad_rebuilt`'s rebuilt node is a real `Rvalue::Aggregate` + `Drop`
  terminator; `bad_nonsub`'s sibling call routes through auto-deref
  (`Deref::deref` then `pick`).

## Honesty notes

* The witness is MODEL-ONLY (same tier as `trustir_adt.rs`): the live
  grounder cannot represent an ADT value; the claim is a self-contained,
  freshly-registered, kernel-checked refinement. Named translation premises
  (module doc of `src/trustir_fold.rs`): P-ACYC (an `Arc<Tree>` value is a
  finite tree), P-ARC-DEREF (std's `Arc` deref returns the pointee), and —
  rung B, for the accumulator members — P-ACC-OPAQUE (`HashSet::insert` as
  the uninterpreted total `insertAcc`; the certified claim is the exact
  insert/recursion SEQUENCE, never set semantics).
* RUNG B — NO memo idiom is admitted anywhere in the fold recognizer, so the
  design §4 memo/accumulator disjunction is enforced by construction: a memo
  get/put would be a foreign call receiving folder state and declines
  (`accumulator_escape` / `foreign_value_in_arm`).
* `size`/`sum` measuring "recognized but not FULLY_FAITHFUL" is the honest
  reading of the design doc's rung-A member list against reality: any fold
  COMBINING two unbounded IHs with `+`/`-`/`*` carries a genuinely
  satisfiable overflow VC, so no sound gate can discharge it. The
  overflow-free folds (`xor_all`, `first_leaf`, `tag_xor`) are the corpus's
  FF-reaching members (a noted divergence from the design's "size, sum" —
  members added, none removed).

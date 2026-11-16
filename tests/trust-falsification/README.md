# Trust falsification self-test (mutation gate)

The load-bearing proof that the verifier is *useful*: for every real obligation
the verifier reports PROVED, a buggy variant (deleted guard / widened bound /
dropped precondition) must flip to FAILED. No surviving mutant, no green.

Every fixture runs under **`-Ztrust-policy=certify`** — full static discharge,
the release policy. The development DEFAULT (policy B, 1b920410d9) tolerates an
undischarged obligation whose operation keeps its runtime check and exits 0;
running the gate under that default made two shift-reduction mutants score
`proved` and manufactured a false "false accept" headline on 2026-08-04
(retracted — nothing false was proved; the gate measured the wrong policy).

- `proved/*.rs` — real-obligation fixtures that MUST verify (exit 0).
- `mutant/*.rs` — the matching buggy variants that MUST fail closed (exit 1).

Run: `scripts/trust_falsification_gate.sh` (uses `build/host/stage2/bin/trustc`).
The gate goes RED if any proved fixture fails to verify OR any mutant survives.

## Defined `as` casts (policy 9f4b2c8417)

Defined int `as` truncation compiles with NO obligation (it is defined Rust
semantics and cannot panic). The old lossy-cast proved/mutant pairs were
reconciled: the ex-mutants now live in `proved/` as zero-obligation
ACCEPTANCE fixtures (they emit no verification headline — they gate that the
acceptance persists, not a proof), and the genuinely-panicking coverage moved
to `mutant/cast_trunc_{index_oob,div_zero,guarded_index_oob}.rs`.

**✅ RESOLVED P0 (found 2026-07-06 during that reconciliation; fixed same
day):** the enum discriminant-set fact was carried across a narrowing cast
WITHOUT mod-2^8 truncation and intersected with the target-type range, so a
`#[repr(u16)]` enum with discriminants `{0, 260, 512}` indexing
`a[e as u8 as usize]` on a len-4 array FALSE-PROVED (1 proved, rc=0) yet
panicked at runtime (260 as u8 == 4). FIXED in
`trust-vcgen::generate::build_discriminant_variant_range_facts`: the
cast-destination fact is now the tags' IMAGE under the exact `as` semantics
(`truncate_nonneg_tag_as_int`, mod 2^dest_width + sign reinterpretation), so
the witness now lives at `mutant/enumdf_castnarrow_oob.rs` and MUST refute.
Siblings: `proved/enumdf_u16_castnarrow.rs` (all tags ≡ 0 mod 256 — genuinely
safe, stays proved) and `proved/enumdf_castnarrow_fits.rs` (tags fit u8 — the
fold is the identity, stays proved).

## The sibling-obligation pairs

Four mutants come in two near-identical pairs, and the near-identity is the
fixture:

| alone | with a provable sibling |
|---|---|
| `unbounded_alloc_const_oom.rs` | `sibling_arith_masks_alloc_ceiling.rs` |
| `undocumented_unsafe_sig_call.rs` | `sibling_arith_masks_unsafe_demand.rs` |

The right-hand variants add one obligation that genuinely proves. That is the
only difference, and it is the whole point: trust-mc's native lane translates the
WHOLE FUNCTION into one Horn rule set, so a provable sibling makes the rule set
non-trivial and makes the solve return safe. An allocation-budget violation and
an unsafe-op demand are not panic edges, so neither appears in those rules —
crediting them from that one solve reads "the solver found no counterexample to a
question it was not asked" as a proof. Alone, both obligations refute, which is
exactly why the shape survived earlier hunts: the defect is invisible in the
isolated case.

Do not "deduplicate" a pair by deleting the plain variant. The pair is a
differential: the plain one shows the obligation refutes on its own merits, the
sibling one shows the whole-function solve cannot launder it.

## Folded-to-`false` asserts, and the reason the naive spellings are not vectors

`x << 64` and `a[4]` are COMPILE ERRORS: `arithmetic_overflow` and
`unconditional_panic` are deny-by-default, so neither spelling ever reaches the
verifier and neither is a vector. A statically-false `Assert` condition arrives
by a route those lints do not evaluate — they run pre-monomorphization, and they
do not fold a `const fn` call at its use site. Three such routes are known and
each has a row; nothing here claims the list is exhaustive:

| route | fixture |
|---|---|
| const generic, shift amount | `mutant/sd_shl_const_generic_overflow.rs` |
| const generic, array index | `mutant/sd_array_index_const_generic_oob.rs` |
| `const fn` folded by MIR const-prop, not by the use-site lint | `mutant/sd_shl_constfn_overflow.rs` |

Measured under stock rustc 1.96.0, all three compile with ZERO warnings and
panic on 100% of their swept domains (64/64 runs each). Their point is that a
const evaluator must compare the folded condition against the terminator's
`expected` rather than merely observe that it IS constant: the two const-generic
bodies carry `Lt(const N, const 64_u32)` / `Lt(const I, const 4_usize)`, which at
`N = 64` and `I = 4` fold to `false` against an `expected` of `true`, and the
`const fn` row reaches the back end as a literal
`assert(const false, "attempt to shift left by `{}`, which would overflow", …)`.
Discharging on constancy alone certifies all three.

Three completeness twins stop that comparison from degenerating into "refuse
every constant assert": `proved/sd_shl_const_in_range.rs` (`x << 32`),
`proved/sd_shl_const_boundary.rs` (`x << 63`, the last in-range shift for a
`u64`: an evaluator using `Le` where rustc's lowering uses `Lt` agrees with a
correct one on `x << 32` and on `x << 64`, and separates from it here) and
`proved/sd_array_index_const_in_range.rs` (`a[2]` on a
`[i32; 4]`, the twin of the const-generic index mutant).

Two def-count rows sit beside them. `mutant/sd_shl_two_def_branch.rs` and
`mutant/sd_array_index_two_def_branch.rs` give the shift amount / index TWO
constant defs on opposite branches, one safe and one faulting: a resolver that
folds to ONE of them certifies a function that panics on half its input space
(64 panics / 128 runs, all on the same branch). `mutant/sd_shl_param_unbounded.rs`
is the ZERO-def end of the same spectrum — a parameter's entry definition is not
a statement in `body.blocks`, so a def-counter walking blocks sees no defs at
all. The single-operand form of that last shape was already covered by
`mutant/left_shift_guarded.rs`; the row is here for adjacency to the other two.

## Hidden non-prefix obligations

`mutant/ep_hidden_obligation_divzero.rs` and
`mutant/ep_hidden_obligation_bounds.rs` each give a callee TWO asserts: one in
the ENTRY PREFIX, chargeable to the caller, and one behind a branch. The caller
passes an argument that DISCHARGES the prefix obligation and says nothing about
the second, which fails (32 panics / 64 runs each, every panic on the branch).

They exist so that any relaxation of the all-or-nothing entry-prefix rule has to
CHARGE the non-prefix assert rather than drop it. Dropping it certifies a caller
whose callee panics on half its inputs — the hidden-obligation class the
all-or-nothing rule exists to prevent.

## What this gate CANNOT see: declined rows in the trust-clean certification tiers

There is a false-proof class this corpus is structurally unable to cover, and
saying so is part of the corpus's job. A DECLINED row (`UnsupportedMir`, e.g.
`UnmodeledCalleeReturn`) carries a `Bool(false)` placeholder formula; read as a
formula rather than as a KIND, it "discharges" via `RefutedModulo3`, and a
function whose entire safety-VC set is declined reads as vacuously discharged
over an empty filtered set. Two ways for a certification tier to certify a body
it never proved.

**A `.rs` fixture cannot reach it**, for three independent reasons, each checked
rather than assumed:

1. Those tiers live in the **`trust-clean`** crate. `trust-clean` is not in the
   compiler's link closure — the compiler crates depend on `trust-clean-carrier`
   and `trust-clean-origin`, and neither of those depends on `trust-clean`. The
   gate drives `trustc`; `clean` is a separate binary the gate never invokes.
2. Under the gate's `-Ztrust-policy=certify`, a declined row is a build error.
   Measured on a body whose only unproved row is exactly the decline
   (`a / f()` for `f: &dyn Fn() -> u32`, whose return is an
   `UnmodeledCalleeReturn`): the compiler answers `incomplete`, never `proved`.
3. `classify_verdict`'s `contains_incomplete_static_accept` is a second,
   independent refusal to read such an exit as `proved`.

So the coverage belongs in a crate test, and it is already there:
`crates/trust-clean/src/decline_gate_tests.rs` covers both channels by name —
`declined_row_blocks_the_safety_discharge_gate`,
`declined_row_trips_the_unmodeled_safety_gate`,
`no_declined_row_carries_a_refutable_placeholder` (which pins the
`RefutedModulo3` spelling itself),
`declined_row_blocks_the_trustir_safety_faithfulness_gate` (the empty-filtered-set
channel), and the `decline_free_controls_keep_their_verdicts` control. Add to
that file, not to this corpus.

## Known backend limitations (future fixtures)

Some guarded obligations are sound but the current backends cannot yet PROVE
them, so they are not (yet) gate fixtures — adding them as `proved/` would make
the gate red for the wrong reason:

- **division-by-zero under a `d != 0` guard** — interval does not model division;
  the in-process ay backend returns Unknown for the div-by-zero VC.
- **u32 subtraction underflow under an `a >= b` guard** — ay reports a Farkas
  "potential false-UNSAT" and conservatively returns Unknown (sound: it refuses
  to claim a proof it is unsure of).

These are backend-capability gaps to close, not soundness holes: the verifier
correctly refuses (fail-closed) rather than vacuously passing them.

## Quarantined fixtures — `pending/`

`pending/proved/` and `pending/mutant/` hold fixtures that the gate does **not**
scan (it globs only the top-level `proved/*.rs` and `mutant/*.rs`). Five fixtures
from commit `3cdc665129` — which did not compile when pushed and whose gate was
never run — depend on in-flight T5A / T6 / T9 verifier capability that has not
landed; see [`pending/README.md`](pending/README.md) for the per-fixture
diagnosis and runtime-oracle verdicts. None is a soundness hole (the surviving
`extern_write_unbounded_fd` mutant reports an honest `0 proved, 1 unknown`, not a
false proof, and its program is memory-safe at runtime — `write(fd, NULL, n)` is
`EFAULT`, not UB). Restore each once its backing capability lands.

The one fixture here that DID pin a soundness hole —
`mutant/str_slice_computed_byte_offset_oob.rs`, the str char-boundary
false-accept — was restored to the gated `mutant/` lane on 2026-07-24 once its
fix (`3f93cbb5bd`) was confirmed to refute it. A soundness fixture belongs in
`pending/` only while its fix is genuinely absent; quarantine is for capability
gaps, never for a hole we already closed.

## A gated fixture that is RED on purpose

`mutant/grid_merged_loopvar_index.rs` reports **SURVIVING MUTANT** on both the
pristine base and this branch. It is not a capability gap and it does not belong
in `pending/`: the compiler answers `proved`, with every obligation
kernel-certified, on a body the runtime oracle panics on. An affirmative proof of
a false statement is precisely what this corpus exists to make visible, so the
row stays in the gated lane and the gate stays red until the defect is fixed.
Its safe twin `proved/grid_unmerged_loopvar_index.rs` — same nested loops, same
`y * 3 + x`, no merge — must stay green throughout, so a fix can be told apart
from a blanket refusal. The fixture's own header records the near-neighbour
shapes that do NOT reproduce it, which is the search space a fix has to explain.

## Two gated mutants that score `incomplete` by design (OD-1)

`mutant/absent_callee_call_only_generic.rs` and
`mutant/trait_default_body_generic_caller.rs` print **UNCAUGHT MUTANT:
verification was incomplete** since OD-1 phase 1 (`c77d7678cf`, 2026-10-04).
Their calls are admitted open generic dispatch, so each site mints an
`assumption:instance-hypothesis` row, and certify refuses with `Trust certify
verification failed … 1 instance hypothesis row(s) — … assumed, not proved`.
That header is an INCOMPLETENESS refusal: nothing was refuted, and with no
concrete instance in the crate there is no counterexample to exhibit. The default
and strict policies exit 0 with a warning (the crate's result is CONDITIONAL).

Until 2026-10-06 the classifier did not know the `certify` word and scored both
rows `tool-error`. It now scores them `incomplete`. The word is in the
incompleteness predicate only: adding it to the counterexample predicate would
pass the mutant lane on an assumption refusal, which is the laundering the
2026-07-30 `refuted`/`incomplete` split exists to prevent
(`classify_verdict_test.sh` pins both halves). The rows stay in the gated lane
and keep the gate red. Moving them out would shrink the mutation denominator to
turn the gate green (docs/DECISION_QUEUE.md FALSIF-OD1-VOCAB).

## The static-accept armor reads whole summary lines

An exit-0 compile is `proved` only if every `Trust verification:` line is exactly
`note: Trust verification: P proved, 0 failed, 0 unknown, 0 timed out, 0
runtime-checked[, A assumed (requires)] out of N obligation(s)` with `P + A == N`,
and no `warning: Trust verification advisory for …` or `warning: Trust Level 0
safety verification incomplete for …` line was printed. `assumed (requires)` is
static: it is a definition-entry contract premise that certify charges at every
in-crate call site and itself accepts (docs/DECISION_QUEUE.md
FALSIF-ARMOR-ASSUMED). Every other shape fails closed: `, N skipped`, `, N assumed
(instance discharge)`, the coroutine label `conditionally discharged (NOT proved)`,
another severity, trailing text, counts that fall short of the total, and any
column added later. A proved lane in which no fixture printed a summary at all is
a FAIL row of its own, so a renamed summary cannot turn every fixture into a
zero-obligation acceptance. `scripts/tests/trust_falsification_gate_main_test.sh`
drives the gate's `main()` against a fake compiler to pin these rows.

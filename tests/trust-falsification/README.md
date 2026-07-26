# Trust falsification self-test (mutation gate)

The load-bearing proof that the verifier is *useful*: for every real obligation
the verifier reports PROVED, a buggy variant (deleted guard / widened bound /
dropped precondition) must flip to FAILED under the default strict policy. No
surviving mutant, no green.

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

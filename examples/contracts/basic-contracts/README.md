# Basic Contracts

This is the Tier 2 compiler-owned contract corpus for Trust.

It pins the ratified “one program, two languages” Rust surface:

- first-class `requires` and `ensures` signature clauses
- no imports, shim crates, attributes, or string-parsed specifications
- typed clauses delivered through the compiler's `trust_contracts` query
- crate-local `trust.toml`

## Run It

From this directory:

```bash
targo --unverified check
targo trust check --format json
```

`targo --unverified check` explicitly selects the native compatibility lane and
confirms that the compiler parses and type-checks the clauses; it emits no proof
claim. Plain branded `targo check` is intentionally refused rather than silently
producing an unverified artifact.
`targo trust check` consumes the typed compiler transport and fails closed on
unsupported, missing, or inconclusive authored obligations.

## What This Example Is For

- basic preconditions
- basic postconditions
- arithmetic-safety-adjacent APIs
- collections and loop-shaped code in a crate-first layout

## What It Is Not Claiming Yet

- a claim that every clause is already kernel-certified
- a stable loop `invariant`/`decreases` corpus
- an L2 or temporal example

For the enforced single-file regression suite, see `../../verify_*.rs`.

## This crate is an ORACLE — read before editing `src/lib.rs`

`tests/e2e_basic_contracts_smoke.sh` and the `native-contracts-pipeline-v2`
domination lane (`targo-trust/src/trust_added/pipeline_v2.rs`) assert on this
crate's exact verification outcome. Two hard constraints follow.

### 1. Clause line numbers are pinned

`pipeline_v2.rs` maps each specified function to the source line of its clause:
`divide_exact` → 7, `abs_total` → 13, `get_at` → 26. Anything inserted *above*
those lines — including a doc comment — breaks the lane. Put explanatory prose
here instead.

### 2. `divide_exact` is a DELIBERATE refutation fixture — do not "repair" it

It carries two independently true counterexamples:

1. `ensures result * denominator == numerator` is **false for inexact
   division**: `7 / 2 = 3`, and `3 * 2 = 6 != 7`.
2. `arithmetic overflow (Div)`: `i32::MIN / -1` overflows and panics, and
   `requires denominator != 0` does not exclude it.

As of the 2026-07-20 solver work, (2) is the **only hard refutation** — (1) now
reports `unknown` rather than `failed`. Adding `requires denominator > 0` would
discharge (2) and leave the corpus with **zero** hard refutations, silently
converting a refutation oracle into a coverage-gap oracle that stays green
while the verifier regresses. Both the shell oracle and `pipeline_v2`'s
`PINNED_FAIL_CLOSED_FUNCTIONS` depend on a hard refutation being present.

The e2e's `MUST_NEVER_BE_PROVED` ledger names the exact obligation. If a future
change legitimately makes one of these provable, the ledger entry and the
source change land in the **same commit**, with the reasoning recorded.

### Why `running_total` uses `saturating_add`

It accumulates `u64` over a `&[u32]`; the type permits ~2^32 elements, so a
plain `total += u64::from(*value)` can genuinely overflow and the verifier
**refutes** it — correctly, for an unbounded accumulation with no length
premise. `saturating_add` makes the arithmetic total, which is the honest
repair. `wrapping_add` would also silence the verifier, by converting a
detected overflow into silent wraparound — teaching precisely the anti-pattern
this corpus exists to catch. A length premise was tested and does **not** work:
the accumulator is havoc'd at the loop head, so the premise is inert.

`running_total` and `midpoint_checked` are deliberately **unspecified** public
APIs; the standalone inventory lane pins them as such. Do not add clauses.

Known residual: `running_total` keeps one `unknown` because the lowered bundle
does not contain `core::num::<impl u64>::saturating_add`, so the absent-callee
assumption fires. That is a std-body coverage gap, tracked separately.

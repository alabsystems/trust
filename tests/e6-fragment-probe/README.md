# E6/E9 fragment probe

What the two-language surface actually admits — measured, not described.

```bash
python3 tests/e6-fragment-probe/run.py
python3 tests/e6-fragment-probe/run.py --filter select
```

Exit code is non-zero when any probe's measured verdict differs from the
`probe-expect` in its header.

## Why this exists

The E6 admission fragment is much narrower than the prose around it, and the
boundary is not where a reader would guess. A paragraph describing it goes stale
the moment someone widens a recognizer; this matrix cannot, because it is
re-derived from the compiler on every run.

Each probe is a focused Rust/Clean pair written so exactly one thing about it
is interesting. The runner
records, per function, whether E6 **admitted** it (and as which shape) and
whether an `ensures` **discharged** by uncited definitional equality or a cited
theorem.

## The matrix, as of 2026-07-26

**11 of 32 probes discharge.** The checked-in `probe-expect` headers are the
ratchet; `run.py` must report zero deviations for the compiler being measured.

| verdict | n | meaning |
|---|---|---|
| `discharged` | 11 | the kernel closed the clause by defeq or a cited theorem |
| `clause-outside-fragment` | 9 | the clause never reached the kernel |
| `defeq-rejected` | 6 | the kernel checked a constructed `Eq.refl` and refused it |
| `unproved` | 4 | no defeq attempt reached; obligations left unproved |
| `island-only` | 2 | the island kernel-checked; the probe has no clause to discharge |

The split between the middle two rows is the most useful thing here.
`clause-outside-fragment` is the *elaboration* boundary — an unsupported domain,
a generic, a reference, an unadmitted callee — and it accounts for nearly half
the corpus. `defeq-rejected` means the machinery worked and the terms genuinely
did not match. Collapsing them, as an earlier version of this runner did, hides
where the boundary actually is.

## What discharges

Projection and use-chain identities over `Bool` and unsigned ints of width
8/16/32/64, with or without a `requires` alongside (`d01`–`d05`);
conjunctive clauses whose individual conjuncts match (`d08`/`d09`); and natural
unsigned `Select` spellings (`f01`/`f02`); and compiler-authenticated unsigned
wrapping arithmetic/composition (`f10`/`f21`). `f21` runs under `-O`: the MIR
inliner must preserve the authenticated core calls through Trust verification
instead of erasing them into ordinary overflow-obligated `Add`/`Mul`.

## The three findings this corpus pins

**1. Natural `Select` now discharges.** `f01` writes
`if a < b then a else b` and closes without a helper theorem. The mint uses
Clean's own `ite` term, and `d11` pins the machine-ordering agreement on which
that defeq result depends. `d06` deliberately retains the former
`Bool.rec`/`Nat.ble` encoding and now rejects: changing the canonical encoding
is a visible compatibility event, not a silently counted widening.

**2. Call closure is exact and fail-closed, including a closed S3/S4 lane.**
Certified same-unit callees and compiler-marked modeled intrinsics may
participate in facet closure; impostors, recursion, and unknown callees do not.
For S3/S4, rustc separately authenticates the exact inherent `core`
`wrapping_add`/`wrapping_sub`/`wrapping_mul` definitions over
`u8`/`u16`/`u32`/`u64` and stamps a closed marker distinct from the intrinsic
marker. Every consumer rechecks its grammar and exact width/type agreement.
`f10` pins one arithmetic operation and `f21` pins a composed chain. Unmarked
paths, source lookalikes, malformed markers, signed/`usize`/`u128` carriers,
and mixed-width chains remain refused. `f11` is the ordinary unknown-callee
negative control.

**3. Every constant-shaped probe fails.** `f04`–`f09` cover the arity-0 mint, a
constant reached through an ignored parameter, an explicit `UInt64.ofNat`, a
zero-arity def, and an identity applied to a literal. None discharge. The
`ConstantUint` shape is recognized and admitted, so the defect is downstream of
admission.

`d12` separately pins item 10 phase 1: a stateful island suffix may name the
compiler-minted `trust_import_*` function and is checked after the matching
program admission exists. It is intentionally `island-only`.

`d13` pins the phase-2 authority boundary. Reusing the authoritative
`FileContext` is necessary but not sufficient: the in-walk clone contains a
partial set of program admissions, while the authoritative island check runs
against the complete post-walk environment. Deferred text must not discharge a
clause until exact context, model, facet, admission, and complete-inventory
parity are established *before* any report, cache entry, evidence row, or
trust-authorized MIR rewrite can escape. The current compiler therefore leaves
the clause unproved.

## Adding a probe

Give it a header and keep it minimal:

```rust
//@ probe-shape: Projection          // the shape you expect E6 to recognize
//@ probe-expect: discharged         // discharged | defeq-rejected |
                                     // clause-outside-fragment | unproved |
                                     // island-only | compile-error
//@ probe-note: one line on why this probe is worth its place
```

A probe should isolate ONE variable against a probe that already passes. If it
fails for two reasons at once it tells you nothing you can act on.

## When a probe starts passing

That is the point of the corpus, and it is why the runner exits non-zero on any
deviation rather than only on regressions. A widening should never land
silently: when any expected frontier starts discharging, this runner fails, and
whoever widened the fragment updates the expectation **in the same commit** —
which makes the diff say, in one line, exactly what the compiler can now prove
that it could not prove before.

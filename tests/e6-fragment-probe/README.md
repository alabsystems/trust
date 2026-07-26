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

Each probe is four to eight lines pairing a Rust function with a Clean island
definition, written so exactly one thing about it is interesting. The runner
records, per function, whether E6 **admitted** it (and as which shape) and
whether the uncited `ensures` **discharged** by definitional equality.

## The matrix, as of 2026-07-25 (toolchain `c6be27eb8`, aarch64-apple-darwin)

**6 of 24 probes discharge.**

| verdict | n | meaning |
|---|---|---|
| `discharged` | 6 | the kernel closed the goal by defeq |
| `clause-outside-fragment` | 11 | the clause never reached the kernel |
| `defeq-rejected` | 5 | the kernel checked a constructed `Eq.refl` and refused it |
| `unproved` | 2 | no defeq attempt reached; obligations left unproved |

The split between the middle two rows is the most useful thing here.
`clause-outside-fragment` is the *elaboration* boundary — an unsupported domain,
a generic, a reference, an unadmitted callee — and it accounts for nearly half
the corpus. `defeq-rejected` means the machinery worked and the terms genuinely
did not match. Collapsing them, as an earlier version of this runner did, hides
where the boundary actually is.

## What discharges

Projection and use-chain identities over `Bool` and unsigned ints of width
8/16/32/64, with or without a `requires` alongside (`d01`–`d05`) — and `Select`,
but only in the form `d06` shows.

## The three findings this corpus pins

**1. `Select` discharges only in the kernel's internal encoding.** `d06` and
`f01` are the *same program*. `d06` writes the island as
`Bool.rec (motive := fun _ => UInt64) b a (Bool.not (Nat.ble (UInt64.toNat b) (UInt64.toNat a)))`
and discharges. `f01` writes it as `if a < b then a else b` — the way a person
would — and the kernel answers *"the two sides are not definitionally equal
(Eq.refl does not check)"*. Until that closes, the second language is not
writable by hand.

**2. Two of the five body shapes are unreachable.** `f10` is the `Arithmetic`
shape: the recognizer matches it, and admission still refuses, because the shape
is built out of a `wrapping_add` **call** while the facet gate poisons on any
`Terminator::Call`. The `Composed` shape (S4) is the same story. `f11` shows the
same wall from ordinary code — a body that calls anything cannot be admitted,
which excludes essentially all real Rust.

**3. Every constant-shaped probe fails.** `f04`–`f09` cover the arity-0 mint, a
constant reached through an ignored parameter, an explicit `UInt64.ofNat`, a
zero-arity def, and an identity applied to a literal. None discharge. The
`ConstantUint` shape is recognized and admitted, so the defect is downstream of
admission.

## Adding a probe

Give it a header and keep it minimal:

```rust
//@ probe-shape: Projection          // the shape you expect E6 to recognize
//@ probe-expect: discharged         // discharged | defeq-rejected |
                                     // clause-outside-fragment | unproved |
                                     // compile-error
//@ probe-note: one line on why this probe is worth its place
```

A probe should isolate ONE variable against a probe that already passes. If it
fails for two reasons at once it tells you nothing you can act on.

## When a probe starts passing

That is the point of the corpus, and it is why the runner exits non-zero on any
deviation rather than only on regressions. A widening should never land
silently: when `f01` starts discharging, this runner fails, and whoever widened
the fragment updates the expectation **in the same commit** — which makes the
diff say, in one line, exactly what the compiler can now prove that it could not
prove before.

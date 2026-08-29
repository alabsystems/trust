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

## The matrix, as of 2026-08-28 (trustc `4c8a1e19da`)

**19 of 46 probes discharge.** The checked-in `probe-expect` headers are the
ratchet; `run.py` must report zero deviations for the compiler being measured.

| verdict | n | meaning |
|---|---|---|
| `discharged` | 19 | the kernel closed the clause by defeq or a cited theorem |
| `clause-outside-fragment` | 15 | the clause never reached the kernel |
| `unproved` | 7 | no defeq attempt reached; obligations left unproved |
| `defeq-rejected` | 3 | the kernel checked a constructed `Eq.refl` and refused it |
| `island-only` | 2 | the island kernel-checked; the probe has no clause to discharge |

Two things about this table are worth more than the numbers.

**It had been unmeasurable, and said nothing about that.** The runner defaulted
to `rustup run trust trustc`, and on at least one machine the `trust` toolchain
is a dangling symlink to a `stage2` that was never built. `rustup` then fails,
`-vV` yields no `commit-hash`, and every probe is classified `unproved` — a full
table of verdicts produced by a compiler that never ran, exiting as if measured.
`run.py` now REFUSES (exit 2) when it cannot identify a trustc. The counts above
are the first live re-measurement in a while, and they moved: the previous
"11 of 32" was header-derived.

**Six constant headers had moved in the same direction.** `f05`-`f09` first
exposed stale `clause-outside-fragment`/`defeq-rejected` expectations. Current
main also closes `f04`, the bare nullary-citation spelling, through the explicit
fail-closed fix in `a96eb1205d`. Every clause is true, and the negative controls
remain refused, so these are real fragment widenings rather than flattering
misclassifications. They stayed invisible because the corpus was measuring
nothing.

### The `g` family: can this surface say anything about the Clean kernel?

Nine probes added 2026-08-28. **0 of 9 discharge.** Seven isolate one variable
each (`g01` shift, `g02` cast, `g03` comparison-returned-as-value, `g04` struct
field projection, `g05` match on a user enum, `g06` self-recursion, `g07` `&self`
receiver); two carry a real clean-kernel body verbatim (`g08`
`ExprMeta::has_loose_bvars`, `g09` `Level::is_zero`). Those two bodies are not
arbitrary — they are the ONLY two that hold a full ten-criteria crystal
scorecard, i.e. the strongest end-to-end results the other route has.

`g08` is refused even with a well-formed Rust clause, so for that body the
surface fails at BOTH ends: the postcondition cannot be *stated* in the spec
expression language, and the body cannot be *admitted*. Until the `g` family
moves, a fused proof about a deployed kernel function cannot be attempted at
all — not "is hard", cannot be attempted.

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
unsigned `Select` spellings (`f01`/`f02`); constant-valued definitions cited
either bare at arity zero (`f04`) or as a call (`f05`–`f09`); and
compiler-authenticated unsigned
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

**3. The constant class discharges in both citation spellings.** This row said
"every constant-shaped probe fails" until
2026-08-22. It was never a kernel limit: `5d63ff80ad9` measured the bare kernel
ADMITTING the constant shape in both spellings and located the defect
**upstream of defeq**, in two places. Both are now fixed, and `f05`–`f09`
discharge:

* `74f315aa368` — the `ConstantUint` routing ERASED ARITY, so a parametered
  constant got a nullary side B (`d` against `d → d`) and the comparison was
  lost before it began. It now mints `fun p0 … => v`. That is `f05`.
* `0acfcc223a2` — a VARIABLE-FREE clause atom (`answer() == c42(0)`) defaulted
  to `Domain::Nat`, minting an ill-typed `Eq Nat` over `UInt64` terms, which
  the kernel rightly refused even though the two sides *were* definitionally
  equal. The atom's domain now comes from term evidence — an admitted callee's
  recorded return domain, a suffixed literal — and conflicting evidence fails
  closed. That is `f06`–`f09`.

* `a96eb1205d` — a bare zero-arity citation now resolves through the same exact
  ambient admission as the called spelling. Bound variables still shadow
  admissions, parameterized definitions still require application, and unknown
  bare identifiers still fail closed. That closes `f04` without widening the
  authority boundary.

Falsified before the expectations were moved (2026-08-22, 15 negative controls,
all REFUSED with the build failing): wrong def value, wrong body value, wrong
call argument, off-by-one at `u64::MAX`, a `u8`/`UInt64 := 256` wrap-launder
attempt, `Nat`-vs-machine and `U32`-vs-`U64` domain mismatches, a mixed
param-domain signature, and — the sharpest one — an identical clause and
identical island def with only the Rust body changed from `42` to `x`. The
discharge is anchored to the MIR body, not to the clause.

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

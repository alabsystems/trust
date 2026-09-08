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

## The matrix, as of 2026-08-26

**44 of 82 probes discharge.** The checked-in `probe-expect` headers are the
ratchet; `run.py` must report zero deviations for the compiler being measured.

| verdict | n | meaning |
|---|---|---|
| `discharged` | 44 | the kernel closed the clause by defeq or a cited theorem |
| `clause-outside-fragment` | 21 | the clause never reached the kernel |
| `unproved` | 8 | no defeq attempt reached; obligations left unproved |
| `defeq-rejected` | 6 | the kernel checked a constructed `Eq.refl` and refused it |
| `island-only` | 2 | the island kernel-checked; the probe has no clause to discharge |
| `other` | 1 | a native refutation; see `f53` |

The counts above are the CHECKED-IN EXPECTATIONS, and the table had drifted from
them badly before 2026-08-26 (it read "25 of 57" while the corpus held 73 probes
of which 35 discharged). It is now re-derived from `matrix.json` rather than
edited by hand, and the `d*` probes — 16 of the 82 — are counted, which the old
number did not do.

## Both surfaces, or half a measurement

Every probe up to `f64` spells its clause in SIGNATURE position
(`fn f(..) -> T ensures P { .. }`). That is not the surface a real crate uses: a
crate that must still build under stock rustc writes
`#[cfg_attr(feature = "trust-surface", trust::ensures(P))]`, and until `f65`/`f66`
nothing here measured whether the attribute spelling reached the same lane. It
did not, in general — an uncited attribute `ensures` in the `result` spelling was
refused by the snippet lowerer, left `Unsupported` sentinel obligations, and a
non-strict policy downgraded those to warnings, so a violated contract compiled
GREEN. `f65` pins that the attribute form now reaches the defeq lane and `f66`
pins the half that matters: the same uncited attribute clause over the wrap bug
the guard exists to catch can never read `discharged`. Probes that name
`#[trust::` get the in-tree `tests/ui/contracts/auxiliary/trust.rs` passthrough
shim supplied automatically by the runner.

`f58`–`f62` are the two 2026-08-26 recognizer increments. Four of the five —
`f58`, `f59`, `f61`, `f62` — already MEASURE their recorded verdict on the
compiler that predates the increments, so they are pinned, not predicted: what
they add is the E6 column (`recognize=`) and the refusals, not a verdict change.
`f60` is the single row that is a PREDICTION until the compiler carrying the
increments is built: it expects `discharged` and measures
`clause-outside-fragment` without the `WidenedEq` mint. If it does not flip, the
`discharged` count above is 35 and this header is what gets corrected.

The split between `clause-outside-fragment` and `defeq-rejected` is the most
useful thing here. `clause-outside-fragment` is the *elaboration* boundary — an
unsupported domain, a generic, a reference, an unadmitted callee, or a goal the
kernel cannot type. `defeq-rejected` means the machinery worked and the terms
genuinely did not match. Collapsing them, as an earlier version of this runner
did, hides where the boundary actually is.

`clause-outside-fragment` grew from 15 to 19 on 2026-08-25, entirely from
increment 7's four deliberate negatives (`f39`–`f42`); nothing that used to
reach the kernel stopped reaching it.

`defeq-rejected` shrank from 6 to 2 on 2026-08-23, and not because anything
started proving: the ill-typed-goal gate moved `f06`–`f09` into the row they
always belonged in. Those goals never typechecked — a variable-less atom takes
the Nat domain, so a `UInt64` island call sat under an `Eq Nat` — and the defeq
route used to reach the judgment and report "not defeq", which reads as a near
miss rather than a clause that was never in the fragment. It grew again on
2026-08-24, this time on purpose: `f29` and `f32` are negatives that MUST stay
red (see finding 4 below).

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

Since 2026-08-23, `Select` also discharges at a SIGNED carrier (`f25`): `i8`–`i64`
admit as the exact two's-complement `BitVec w`, with comparisons — in the minted
body and in the elaborated goal alike — stated over the sign-flip order keys
`Nat.xor (BitVec.toNat v) 2^(w-1)`. Clean's own `BitVec` order instances are
UNSIGNED and are deliberately not reused, because they would give the program's
signed `<` an unsigned meaning at `i64::MIN`.

Since 2026-08-24 the sibling COMPARISON-TO-BOOL shape discharges too, in both
spellings and at three carriers. `f26` is the one that flipped: its body minted
a release earlier and no clause could reach it. `f27` is the spelling an author
reaches for — `ensures result == (a <= b)` with no theorem — which now closes by
reflexivity because the clause's nested comparison elaborates to the very
`Decidable.decide` term the mint emits. `f28` is the unsigned twin and pins the
`>=` operand swap. `f33`/`f36` are the same lane at `i128`, the exact-arithmetic
tier a fixed-width checker computes its overflow guards in. `f34`/`f35` pin a
LITERAL bound (`x >= 0`, `x >= -1`) — the shape every width guard is actually
written in — with the negative one carried by magnitude, never as a wrapped
`u128`.

Since 2026-08-25 a clause may finally mention an AGGREGATE: `c.degree` is a
DOTTED-PATH SCALAR BINDER (`f37`, `f38`, `d15`). It is one OPAQUE SCALAR ATOM —
a variable named by its path and bound at the FIELD's carrier — so the goal is
the same term the undotted spelling produces and no struct ever reaches the
kernel. The compiler contributes a binding row per scalar field of every
parameter, and a body mint (`AdmissibleBody::FieldProjection`) that takes one
binder per row: `fn degree_of(c: Cst) -> u64 { c.degree }` becomes
`fun (degree : UInt64) (coeff : UInt64) => degree`. `d15` is the shape the
veripb client needs, at the real `i64` width and with the same `key64` sign-flip
order key its saturation theorems already use.

Since 2026-08-26 two more shapes are recognized, both taken from the veripb
client's blocked list.

A SIGNED constant (`f58`) — `fn zero() -> i64 { 0 }` — was refused for one
reason: `ConstantUint` matched `ConstValue::Uint`, and a signed literal extracts
as `ConstValue::Int(i128)`, sign-extended and carrying NO WIDTH. The new
`ConstantInt` shape takes the carrier from the DECLARED return type (pinned
signed, pinned to agree with `_0`'s own declared type) and range-checks the
value against it. It mints the term a clause spells for that literal, arm for
arm: `Domain::zero` at `0`, `numeral` above it, `negative_numeral` on the
MAGNITUDE below it — so `-1` is the two's-complement pattern, never `1`. Note
what this does NOT change: no constant-shaped probe discharges, before or after,
because a variable-less clause atom still defaults to the `Nat` domain (`f04`–
`f09`). The forgery pins therefore live in the trust-certify def-eq oracle,
which does reach the judgment; `f58`/`f59` are a PAIRED deferred ratchet for the
day the constant clause lane opens.

A MIXED-WIDTH comparison with a widening CAST operand (`f60`) — `fn eq_ok(m:
i64, t: i128) -> bool { Wide::from(m) == t }` — is the one shape
`ComparisonBool` structurally cannot reach: its operands are a parameter or a
literal at ONE carrier. The mint models the cast as SIGN EXTENSION, spelled as
the checked lane's own exact-`Int` bridge composed
(`ofInt128 (toInt64 v)`) — no new primitive, exact on all 2^64 inputs. The two
NEGATIVES are the whole faithfulness story: `f61` is the same MIR shape in the
TRUNCATING direction, and `f62` is the same MIR shape BYTE-FOR-BYTE with a `u64`
source, i.e. ZERO extension. Nothing in the MIR distinguishes `f62` from `f60`;
the declared signedness of the source local is the only discriminator, and zero
and sign extension differ on exactly the negative half of the domain.

Two authoring facts fell out of writing the COMPARISON-TO-BOOL probes, both
recorded in the probes rather than in prose: the uncited defeq route owns only
clauses that CALL an island definition, so `f27`'s conjunction is what makes it
measurable at all;
and a large numeral in a hand-written island (`BitVec.ofNat 64
18446744073709551615`) does NOT elaborate to the kernel literal the mint builds,
while the `Nat.zero` spelling in `f34` does.

## The seven findings this corpus pins

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

**4. Two negatives keep the comparison encoding honest.** `f29` is `f27` with
one conjunct's operands reversed and `f32` is `f26` with the island rewritten to
`Nat.ble` — a spelling true of exactly the same pairs. Both must stay
`defeq-rejected`. On neutral arguments `Nat.ble x y` and
`Decidable.decide (Nat.le x y) (Nat.decLe x y)` are stuck at different head
constants, which is an IOTA mismatch no reducibility setting bridges (the
select-encoding lesson again). Re-encode the mint over `Nat.ble` and `f26` goes
red while `f32` goes green: the diff then says in one line which encoding the
compiler speaks.

**5. A call in proposition position is gated on the RECORDED return domain.**
`f31` calls a certified, fully admitted island definition returning `BitVec 64`
as if it were a proposition, and stays refused; only an admission that recorded
`Domain::Bool` reads as `f(a, b) = true`. The island lane records a domain only
for a literal `Bool` codomain, because the Clean-type-to-`Domain` map is not
injective — `BitVec 64` is the carrier of both `i64` and `usize`. `f30` is the
matching net on the other side: `bool` has no ORDER, so a decided bool-valued
operand under `<=` stays outside the fragment.

**6. A dotted path may name a PARAMETER's field and nothing else.** Four
negatives hold the line, and each names a different reason. `f39` is a `&Cst`
parameter: the MIR read carries a `Deref`, and the pointee is not provably
unchanged between entry and exit, so `ensures` has no reading for it. `f40` is
ALL-OR-NOTHING per struct — one non-scalar field refuses the whole parameter,
because the clause-side flattening (HIR types) and the mint-side flattening
(extracted-IR types) are two independent computations of one list, and a
per-field FILTER would be two filters that must agree field by field; a
disagreement would emit the same binders in a different ORDER, and a theorem
about one field would discharge a clause about another. With no filter there is
nothing to disagree about, and a same-length REORDERING is separately refused by
`Admission::param_names`, which records what the mint actually bound. `f41` is
`result.<field>` — the client's own `(satC c).degree = c.degree`; a
parameter-side path is an atom the clause may quantify over, but `result`
denotes the return value only through the E6 import, so projecting it means
projecting the minted term, which needs the aggregate carrier. `f42` pins the
depth: the path is depth 1.

**7. An island numeral below 2^64 is not the literal the mint builds.** `f43`
and `f44` are the same probe on either side of that threshold: `100` is refused
and `2^128 - 100` discharges, with the function E6-admitted and the clause in
the fragment in both cases. Nothing in the source of the red one looks wrong —
the island definition is the mint transcribed by hand. Spelling is not the
lever (`(100 : Nat)`, `Nat.succ 99`, `Nat.add 99 1`, and `Nat.sub`/`Nat.div`/
`Nat.mod` of two above-threshold literals landing below it are all red), while
`Nat.add` landing *above* the threshold is green — the arithmetic reduces, the
resulting value decides. `Nat.zero` is the one exception below the threshold,
which is why `f34`'s `x >= 0` works. The client cost is concrete: a machine
width guard whose bound is a small positive literal cannot be given a contract,
so the veripb kernel can cite the lower bound of its `i64` guard (`i64::MIN` at
128 bits is `2^128 - 2^63`) and cannot cite the upper one (`i64::MAX` is
`9223372036854775807`).

One authoring fact, measured while writing `f38` and worth stating out loud
because it is not about fields at all: the CITED lane installs no
island-definition facets (only the uncited defeq lane does), so
`isl(c.degree) <= c.degree by thm` is refused with "no diagnostic E6 facet
record exists". The citation spelling that works is the client's own — mention
`result`, and state the theorem over the value the E6 import unfolds to.

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

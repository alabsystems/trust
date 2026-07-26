# Two-language conformance battery

A battery of **real programs** that asks, empirically, how much of the ratified
"One Program, Two Languages" design
(the internal 2026-07-09 two-language spec-surface document)
the toolchain actually implements — and reports the answer whether or not it
is flattering.

Run it:

```bash
python3 tests/two-language-battery/run.py           # full battery -> results.json
python3 tests/two-language-battery/run.py --filter lane-c
```

## Why this exists separately from `tests/ui/trust/`

The 172 fixtures in `tests/ui/trust/` are *slices*: each pins one mechanism at
minimum size, which is what regression pins should do. They cannot answer "is
the design implemented?", because a design can be implemented in slices and
still not compose over a program anyone would write.

This battery uses whole, ordinary programs — binary search, Euclid's
algorithm, a ring buffer, an accumulator — and asks whether their contracts go
through.

## The lanes

| Lane | Language surface | Proof authority exercised |
|---|---|---|
| **A** `lane-a-rust/` | Rust first-class clauses (`requires`/`ensures`/`decreases`, loop `invariant`) | native/solver (arithmetic, termination) |
| **B** `lane-b-lean/` | pure Lean in `clean { … }` islands | Clean kernel |
| **C** `lane-c-combo/` | both languages in one file — cited (`by thm`) and uncited (defeq) discharge | Clean kernel |
| **D** `lane-d-legacy/` | legacy kani frontend → tippy migration diagnostic | none (a diagnostic, not a proof) |
| **E** `lane-e-ir-spine/` | both languages, observed **in the emitted TrustIr module** | — (an architecture measurement) |

## The two rules that make it a battery and not a demo

**1. Negative controls, and they must fail for the right reason.**

Half of this battery is programs that MUST be rejected: a false `ensures`
(`a3`), a non-terminating recursion with an authored measure (`a5`), a bogus
Lean proof term (`b2`), a body that diverges from the island definition it
claims to equal (`c3`). A toolchain that accepts these proves nothing by
accepting the positive files either.

But a negative control that fails with a *parse error* or an *unresolved name*
has also proved nothing, while still looking green. So the runner classifies
every failure into exactly one of three kinds, and only one of them counts:

| kind | meaning | scores as |
|---|---|---|
| `refutation` | the proof was refused | `reject-correct` ✅ |
| `frontier` | an `unsupported`/`[unknown]` row — the tool could not MODEL it | never a successful rejection |
| `malformed` | the compiler could not read the program | `reject-wrong-reason` ❌ |

`frontier` exists because of a trap this battery walked into: an UNKNOWN row
means the tool declined to model the program, and scoring that as a successful
rejection lets a **capability gap impersonate a proof**. Frontier beats
refutation when a build reports both, since the build failed *because of* the
unsupported row.

Classification runs over diagnostic prose only — location lines (` --> `) and
source echoes (`NN | `) are stripped first. That is not fastidiousness: every
diagnostic embeds the absolute path of the file under test, which contains the
string `trust`, so an earlier version that matched markers against raw stderr
classified **every** failure as a verification rejection and made
`reject-correct` unfalsifiable.

`b2_NEG_bad_proof.rs` is the most important file here — if the kernel accepts
`Nat.le 1 0`, every Lane B and Lane C pass in this battery is worthless.

**`battery-expect: frontier`** marks a program that is CORRECT and whose
contract is TRUE, but which some lane cannot model yet (`a11` Euclid's `%`
measure, `a12` binary search's multi-path loop body). These are scored as
measurements, not failures, and they flip to `frontier-closed` by themselves
when the fragment grows. A frontier file that starts reporting `refutation` is
an alarm: the tool would be claiming a true clause is false.

**2. Nothing is scored from a stale toolchain.**

`trustc`'s version stamp embeds the superproject HEAD. The runner records the
toolchain commit and the repo HEAD in every scorecard and warns when they
differ, with the commit distance. A re-run against a compiler built before the
fixes under test is the single easiest way to produce impressive, meaningless
numbers.

## Lanes expected to fail today, by design

Two lanes are written against the **target**, not against current behaviour.
They are specifications, and their failure is the measurement:

- **Lane D** expects tippy's diagnostic to contain the Lean the user should
  write instead. Today `legacy_spec_sugar.rs` suggests *Rust clauses only* and
  emits no Lean anywhere user-facing, so this lane fails. It encodes the owner
  directive of 2026-07-24 ("legacy frontends where tippy corrects to Lean"),
  which amends §3.2 of the ratified design and is **pending ratification** —
  so this lane is a stated target, not an agreed requirement.

- **Lane E** expects both languages to appear in one `trust_ir::Module`. From
  source: Rust *does* reach TrustIr directly — `trust_thir_lower` lowers
  source (THIR) straight to trust-ir under a differential gate against MIR
  (`compiler/rustc_mir_build/src/builder/mod.rs:92`) — but the `clean { … }`
  island does not. The module has the slot (`proof_certificates`,
  `ProofEvidence::LeanProof`); no production path fills it from an island. The
  expected verdict is therefore `ir-rust-only`, which is the precise statement
  of what remains to build before "both languages feed the same TrustIr
  module" is true.

## Measured result (2026-07-25, toolchain `c6be27eb88`, matches HEAD)

24 programs. **0 false accepts. 0 rejected-for-the-wrong-reason.**

| verdict | n | meaning |
|---|---|---|
| `pass` | 8 | verified end-to-end |
| `reject-correct` | 5 | a negative control refuted, for the right reason |
| `frontier-confirmed` | 3 | correct program the lane cannot model yet |
| `unexpected-reject` (frontier) | 3 | expected pass; landed on an unmodelled row |
| `unexpected-reject` (refutation) | 1 | `a7` — obligations genuinely refuted, see below |
| `frontier-refuted` | 1 | `a12` — standing alarm, the cascade below |
| `tippy-fires-but-no-lean` | 2 | lane D target unimplemented |
| `ir-rust-only` | 1 | lane E spine gap |

**What works.** Lane B 4/4 and lane C 5/5. Both discharge modes of the combo —
cited (`by thm`) and uncited kernel defeq — verify on real programs, and the
kernel refuses both a bogus `Nat.le 1 0` proof and a well-typed citation that
does not prove the goal. Those two refusals are what make the passes mean
something.

**Where lane A actually stands.** 8 of 12 as specified. The gaps are not wrong
answers: `a6`/`a9`/`a10` land on unsupported rows, and the recurring blocker is
the single-path loop-transition fragment — any loop body doing more than a
trivial statement falls outside it. `a7` is the one genuine refutation of a
program believed correct and is worth a look on its own.

**Two findings the battery produced that are worth more than its score:**

1. *A false loop invariant is currently neither proved nor refuted* (`a8`). It
   lands as `UserLoopContractUnsupported`. Not a false accept — strict policy
   still fails the build — but the E4 surface has no working refutation control
   until the fragment covers a two-statement body.
2. *A fragment gap does not stay contained* (`a12`). When the invariant is
   unmodelled, the obligations depending on it are reported **FAILED**, not
   unknown: binary search's `xs[mid]` is refuted even though `mid < hi <=
   xs.len()` follows from the invariant. A spurious failure, not a false
   accept — the direction that costs trust rather than soundness.

## Reading the scorecard

`results.json` carries, per program: the exact command, exit code, captured
diagnostics, the verdict, and for rejections the failure classification. The
summary counts `false_accepts` (soundness breaks) and `reject_wrong_reason`
(battery integrity breaks) separately — the runner exits non-zero only for
those two, because a documented unimplemented lane is a measurement rather
than a runner error.

Quote no number from this battery without its toolchain stamp.

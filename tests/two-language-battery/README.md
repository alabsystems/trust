# Two-language conformance battery

A battery of **real programs** that asks, empirically, how much of the ratified
"One Program, Two Languages" design
(the internal 2026-07-09 two-language spec-surface document)
the toolchain actually implements — and reports the answer whether or not it
is flattering.

Run it:

```bash
STAGE2=$(cd build/host/stage2 && pwd -P)
TRUST_BATTERY_OUT=$(mktemp -d "${TMPDIR:-/tmp}/trust-two-language-battery.XXXXXX")
TRUST_PROBE_TRUSTC="$STAGE2/bin/trustc" \
  python3 tests/two-language-battery/run.py --canonical \
  --output "$TRUST_BATTERY_OUT/results.json"
python3 tests/two-language-battery/run.py --filter lane-c \
  --output /tmp/two-language-lane-c.json
```

`--canonical` keeps the full reviewed population and all strict toolchain
checks, while writing a new report outside the source checkout. This avoids
changing tracked `results.json` and invalidating the compiler's source lineage
merely by recording a run. Its output directory must already exist; existing
files and racing publications are never overwritten. The historical default
without `--output` still updates tracked `results.json`, but dirties the source
tree after publication. Neither output mode is a G1–G8 acceptance verdict.

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
every failure by its diagnostic evidence, and only a refutation counts:

| kind | meaning | scores as |
|---|---|---|
| `refutation` | an explicit failed obligation or terminal kernel type mismatch | `reject-correct` ✅ |
| `frontier` | an `unsupported`/`[unknown]` row — the tool could not MODEL it | never a successful rejection |
| `malformed` | the compiler could not read the program | `reject-wrong-reason` ❌ |
| `compiler-failure` | the compiler crashed or failed internally | never a successful rejection |
| `unclassified` | no recognizable terminal verdict | never a successful rejection |

`frontier` exists because an UNKNOWN row or timeout does not refute a program.
Scoring either as a successful rejection lets a **capability gap impersonate a
proof**. A reported failed obligation can count as a refutation even if other
obligations are unresolved; that does not credit those other obligations.
A generic kernel rejection wrapper is not a verdict: it can contain resource
exhaustion, missing names or internal failures. Likewise, the word
"counterexample" alone does not establish successful model validation or replay.
Without an actual refutation, unknown verdicts,
timeouts and missing proof authority remain incomplete. A generic "strict
verification failed" message alone is `unclassified`, never `reject-correct`.

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

`trustc`'s version stamp embeds the superproject HEAD. The runner requires an
exact commit match, a clean superproject, and exact recursive submodule pins
before running or writing canonical results. An explicit
`--allow-unsealed-toolchain` escape hatch is exploratory-only and requires a
non-canonical output path. Filtered runs likewise require a scratch output and
cannot truncate `results.json`. A re-run against a compiler built before the
fixes under test is the single easiest way to produce impressive, meaningless
numbers.

The canonical run also requires the reviewed 27-file path/directive manifest,
compiles read-only snapshots of those exact bytes, and records their digest.
Trustc and Tippy must be executable siblings in this checkout's physical
stage2 tree; both binaries are hashed, both version preflights must succeed,
and checkout, submodule, binary, and fixture identities are rechecked before
the scorecard is atomically replaced.
The same requirements apply with `--canonical --output` outside the checkout;
neither `--filter` nor `--allow-unsealed-toolchain` is permitted in that mode.
The report records whether it measured the canonical reviewed battery or an
exploratory selection; the output filename alone does not establish its scope.

## Target lanes and current implementation boundaries

These lanes exercise target behavior. Their current status needs a fresh run
with the pinned compiler; the archived results below are historical:

- **Lane D** expects tippy's diagnostic to contain the Lean the user should
  write instead. Today `legacy_spec_sugar.rs` suggests *Rust clauses only* and
  emits no Lean anywhere user-facing, so this lane fails. It encodes the owner
  directive of 2026-07-24 ("legacy frontends where tippy corrects to Lean"),
  which amends §3.2 of the ratified design and is **pending ratification** —
  so this lane is a stated target, not an agreed requirement.

- **Lane E** expects both languages in one `trust_ir::Module`. Clean-origin
  bodies now enter that module, and `e2_rust_calls_clean_in_ir.rs` exercises
  local Rust-to-Clean linkage. Identity and type guards and a narrow UInt
  arithmetic carrier gate have also landed. Recording or linking a body does
  not establish general carrier faithfulness, Lean-to-Rust calls, cross-crate
  Trust-IR transport, or executable codegen. The next integration target is a
  real `.lean` package plus Rust crate with calls in both directions and full
  proof evidence, as specified in the project's two-language execution roadmap.

**Latest canonical result (kept out of the tracked `results.json`, as above):** `reports/2026-09-27-new-pack-5ab8dcccfcb-measured/results.json` — stage2 at `5ab8dcccfcb`, 2026-09-27, 23/27 as specified, 0 false accepts, 3 blocking (`a5` and `a8` reject-by-frontier, `b2` reject-wrong-reason); its d1 `tippy-emits-lean` was a classifier false green, since fixed in `run.py`, so lane D is really 0/2.

## Archived measured result (generated 2026-07-26, toolchain `c6be27eb88`)

This section and `results.json` record a historical run whose toolchain was
already 24 commits behind its recorded repository HEAD (`f2b7299212`). They do
not describe the current checkout. Regenerate the scorecard after the final
dependency pins and stage2 binaries are sealed. In that archived run, 25
programs produced **0 false accepts** and **0 rejected-for-the-wrong-reason**.

| verdict | n | meaning |
|---|---|---|
| `pass` | 9 | verified end-to-end |
| `reject-correct` | 5 | a negative control refuted, for the right reason |
| `frontier-confirmed` | 3 | correct program the lane cannot model yet |
| `unexpected-reject` (frontier) | 3 | expected pass; landed on an unmodelled row |
| `unexpected-reject` (refutation) | 1 | `a7` — obligations genuinely refuted, see below |
| `frontier-refuted` | 1 | `a12` — standing alarm, the cascade below |
| `tippy-fires-but-no-lean` | 2 | lane D target unimplemented |
| `ir-rust-only` | 1 | lane E spine gap |

**What was as specified.** Lane B was 4/4 and lane C was 6/6. Both discharge
modes of the combo — cited (`by thm`) and uncited kernel defeq — verify on real
programs, and the kernel refuses both a bogus `Nat.le 1 0` proof and a
well-typed citation that does not prove the goal. Those two refusals are what
make the passes mean something.

**Where lane A stood in that run.** 7 of 12 were as specified. The gaps were
not wrong answers: `a6`/`a9`/`a10` landed on unsupported rows, and the recurring
blocker was the single-path loop-transition fragment. `a7` was the one genuine
refutation of a program believed correct and is worth a look on its own.

**Two findings the battery produced that are worth more than its score:**

1. *At that snapshot, a false loop invariant was neither proved nor refuted*
   (`a8`). It landed as `UserLoopContractUnsupported`. **The claim that
   followed here was false, and it is corrected rather than deleted.** It said
   the bad initiation and bad consecution are "genuinely refuted", so `a8` is
   "again an ordinary negative control". Measured on the canonical stage2 run
   at `5ab8dcccfcb` (2026-09-27), `a8` is `reject-by-frontier` and blocking.
   trust_mc's CHC/PDR runner refutes all three bad invariant obligations, and
   each refutation is demoted before it can count: "refutation demoted to
   unknown: the submitted ChcVc has no positive producer fidelity attestation
   … (no loop transition relation is emitted)". The row was already
   unresolved at `6ff31de9b6`
   (`docs/plans/2026-09-07-two-language-execution-log.md`). The fixture keeps
   `battery-expect: reject`, so the row stays blocking (fail-closed) until a
   real refutation lands.
2. *A fragment gap does not stay contained* (`a12`). When the invariant is
   unmodelled, the obligations depending on it are reported **FAILED**, not
   unknown: binary search's `xs[mid]` is refuted even though `mid < hi <=
   xs.len()` follows from the invariant. A spurious failure, not a false
   accept — the direction that costs trust rather than soundness.

## Reading the scorecard

`results.json` carries, per program: the exact command, exit code, captured
diagnostics, the verdict, and for rejections the failure classification. The
summary counts `false_accepts` (soundness breaks) and `reject_wrong_reason`
(battery integrity breaks) separately. The runner exits non-zero for any
unexpected semantic row, identity/inventory failure, or publication failure.
Only the explicitly enumerated current D/E target verdicts are non-blocking
measurements; that does not make their missing product capabilities complete.

Quote no number from this battery without its toolchain stamp. Classification
is diagnostic evidence, not independently replayed proof or a G1–G8 verdict.

The 2026-09-07 runner regression suite has 29 tests, including aggregate
refusals, native UNKNOWN rows, timeouts, absent certificate authority, genuine
counterexamples, echoed verdict words and compiler crashes after a reported
refutation, generic kernel wrappers, exhausted kernel budgets and failed
counterexample replay. A crash, signal or launcher failure cannot satisfy a negative
control. Warning text and wrong-typed Lean options cannot impersonate a proof
verdict. Reclassifying the retained diagnostics of all 25 archived rows changes
no classification compared with the pre-fix classifier. Two truncated rows
(`a7`/`a12`) still cannot reproduce their recorded historical refutation from
the retained text; neither classifier repairs those missing bytes. This checks
reporting stability, not the current compiler.
The external-canonical controls additionally exercise the exact full fixture
inventory at both ends, immutable-source output placement, existing/dangling
output refusal, atomic no-clobber publication, stale/foreign tools, a missing
fixture and postflight compiler drift. These use mocked compiler results to
test runner orchestration; they are not a live conformance measurement.

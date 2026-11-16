# The machine-model gate — operating note

**Before you change `trust-machine-sem` or `trust-disasm`, run this. Before you
land the change, run it again at the full tier.**

```sh
crates/trust-disasm/harness/gate.sh --fast     # ~30 s   — before every commit
crates/trust-disasm/harness/gate.sh            # ~40 min — before landing
```

The full tier is long for one reason only: `native-invariant`'s default tier is
**exhaustive over all 2^32 words**, and that is worth the wall clock. The
semantic differential's full tier is ~22 s. If you only have seconds, `--fast`
runs every stage of both harnesses — including the whole non-vacuity battery —
against smaller populations.

Requires an aarch64 macOS host, clang (Command Line Tools) and the Trust
toolchain's `targo` (resolved and identity-checked by `targo.sh`).
It is deliberately **not** part of `cargo test`: it assembles code, executes
arbitrary instruction encodings and reads a trap `ucontext`. That is a reason to
run it on purpose, not a reason to treat it as optional.

---

## Why this exists

Four soundness families were found one at a time, **each after the previous one
was declared closed**: a discarded `Effect::PcUpdate`, a `1u64 << 64` overflow in
the bitmask decoder, unvalidated reserved fields, and CONSTRAINED UNPREDICTABLE
operand aliasing. Then three more, in the semantics rather than the encoding:
SIMD loads and stores modeled as GPR accesses, `UBFM`/`SBFM` with `imms < immr`
computing an unmasked shift, and `ADCS`/`SBCS` computing flags without the
carry-in.

Every one of them was found by executing instructions on the hardware and
comparing. Nothing else finds them — a mnemonic-level differential compares
*names*, and an aliasing word, a reserved-field word and a wrong-register word
can all carry a correct name.

The thing that made this a seven-time problem is not that the checks were hard.
It is that **they ran once.** A differential that is run, reported and archived
catches the bugs that exist on the day it runs, and then quietly stops being
true. So both harnesses are now gates with committed baselines, and both prove
their own non-vacuity on every run.

## The two harnesses

|  | `native-invariant` | `native-semantic` |
|---|---|---|
| Question | if the gate certifies it, does the CPU **run** it? | if the gate certifies it, does the CPU **do what was certified**? |
| Oracle | fault vs no-fault | whole architectural post-state vs hardware |
| Population | **exhaustive — all 2^32 words** | stratified sample, per-opcode cap |
| Baseline | **0 violations**, and there is no reason for it ever to be anything else | **not zero** — 8 scalar-FP families, recorded |
| Opcodes compared | n/a | **94 of 94** the model accepts |
| Full-tier cost | ~40 min | ~25 s |

**Neither subsumes the other.** All three semantic families passed the invariant
check: they executed perfectly and computed the wrong thing. Running only the
cheap one is how the class survived.

## What the gate actually checks

Three stages, in this order, in both harnesses. **Stage 2 is the one that
matters.**

1. **Ground truth.** Words assembled by clang (semantic), or known-refused
   encodings with their one-register controls (invariant), must come out right.
2. **Non-vacuity.** The differential is re-run against nine deliberately wrong
   models and **every one must be caught**; the invariant sweep is forced to
   process words the CPU demonstrably refuses and **must report them as
   violations**.
3. **The sweep**, checked against the committed baseline.

Stage 2 exists because a broken harness does not report an error — it reports
success. Every degradation these harnesses have suffered had the same shape: a
register file that was never loaded, an exclusion that swallowed a class, a
field that was zero on both sides. In each case the run printed a large
`compared` count and `0 mismatches`, and the number meant nothing.
**A green run is evidence only if a wrong model would have been red.** That has
to be demonstrated on the same run, on the same host — not remembered from the
day the harness was written.

The nine mutations are not hypothetical errors. They are the fault log:
`fp-write-to-gpr` is the SIMD-store bug, `swap-carry-overflow` is the `ADCS`
flag bug, `perturb-reg-value` is the `UBFM` shape, `drop-pc-update` is the
`Effect::PcUpdate` hole. Each is re-injected on every run, so the differential
must keep proving it can still see the bugs that already escaped once.

**A blanket mutation is a weaker guarantee than it looks.** Every entry in the
battery rewrites a whole effect CLASS, so a single word of the right kind
catches it. All three semantic divergences were NARROW and DATA-DEPENDENT, and a
narrow defect needs the triggering word to be in the population before any of
this can see it. The two properties are separate and were measured separately:
three defects written into the SHIPPING SOURCE — the `carry_in AND result == lhs`
disjunct alone deleted from `compute_nzcv_with_carry`, an `LDP` with its two
halves crossed, and `FSUB` computing an addition — each failed the **fast**
tier (`Adcs=25/Sbcs=39`, `Ldp=300`, `Fsub=319`). Repeat that exercise when you
add a family; the battery being green does not say the population is rich
enough.

### Accepted but never compared

Every run now prints the opcodes the MODEL accepts and this oracle never
compared. That set is not the same as "opcodes outside the gate": the output
gate consumes the same effect lists symbolically and can reach Proven on all of
them. It was **eight** — `B`, `Bl`, `Blr`, `Br` and `Fadd`/`Fsub`/`Fmul`/`Fdiv`
— and the consequence was measured, not argued: changing `sem_bl`'s return
address from `pc+4` to `pc+8` (a wrong link register for every call in every
emitted object) **passed the full standing gate, PASS, no new family.** Both
regions are now replayed and the set is empty; keep it empty.

---

## What a failure means

Read the `FAIL:` line — it names the stage. Then:

### `stage 1: the model disagrees with clang-assembled ground truth`
You broke something basic. The corpus is ~99 instructions the assembler chose to
emit. Reproduce the single word:

```sh
cd native-semantic
echo <word-hex> > /tmp/w.txt && ./target/release/natsem-diff --words /tmp/w.txt
```

The report prints `model x5=… native x5=…` for the first disagreeing component.

### `stage 2: mutation 'X' was NOT caught` — **the most serious failure here**
The differential has gone blind to a class of error. Its `0 mismatches` is no
longer about the question it claims to answer. Do **not** proceed to read the
sweep numbers, and do not baseline over it: fix the harness first. The mutation's
name says which state component stopped being compared, and
`Mutation::provenance` in `src/mutate.rs` says which real bug it stands for.

### `stage 3: NEW MISMATCH FAMILY`
A real model/hardware divergence outside the recorded set. Reproduce one word
with `--words`, then choose:

* **fix the semantics**, or
* **REFUSE the form** — return a proof-blocker error from `Aarch64Semantics`.

**Approximating onto a neighbouring value is never acceptable; refusing always
is.** A case silently *accepted* rather than *refused* is a soundness hole with a
delay fuse. Add a value-pinned regression to
`crates/trust-machine-sem/src/aarch64/divergence_tests.rs` — observe it fail
first, and quote the observed output in the test.

### `stage 3: coverage <N>, floor <M>`
Fewer words were compared than the baseline records. Something is being excluded
that used to be checked — read the **blind-spot ledger** printed in the run
output to see which exclusion grew. This is how a harness goes quiet.

### `stage 3: population digest … != recorded …`
A *different set of words* was checked, so none of the counts is comparable to
the baseline. This is a harness or selector change, **not** a model regression;
do not read it as one, and do not `--accept` until you know why the population
moved.

### `VIOLATIONS … > baseline` (invariant harness)
A word the model accepts and the CPU refuses — a potential false Proven, and the
most serious result either harness can produce. `result.violations.bin` holds
the word list; re-check just those with `--words` to characterise the family.

---

## Changing a baseline

```sh
./native-semantic/run.sh --accept          # or --fast --accept
./native-invariant/run.sh --accept         # exhaustive only; refuses --quick
```

**Read the diff before committing it.** Accepting a baseline is accepting every
divergence in it. `native-semantic`'s baseline is deliberately non-zero and says
so at length; `native-invariant`'s is zero and must stay zero.

## Blind spots

Both harnesses carry a normative `BLIND SPOTS` inventory in `src/main.rs`, and
the executors carry theirs in `natsem.c` / `natexec.c`. They are normative in
this sense: **if a limitation is not listed there, the harness is claiming to
cover it.** Adding an exclusion means adding it to that header and giving it a
counter, so lost coverage shrinks a denominator instead of hiding inside an
agreement count.

The short version of what neither harness can see: `FPCR`/`FPSR`, anything
outside EL0, feature-dependent legality on other aarch64 parts (this is one
Apple CPU, no SVE/SME/PAC/MTE), memory ordering and the exclusive monitor, and
`x18` — the Darwin platform register, which the OS resets on some exception
returns. Every one of those is counted or named; none is silently folded into
agreement.

One more is worth stating plainly because it looks like coverage and is not.
`FADD`/`FSUB`/`FMUL`/`FDIV` are now compared, but the concrete replayer performs
the IEEE arithmetic with Rust's `f32`/`f64` operators, which compile to the
host's own `fadd`/`fsub`/`fmul`/`fdiv`. So that comparison does **not**
independently verify IEEE arithmetic and cannot. What it does verify is
everything around it — which register file each operand comes from, which lane
and how wide, whether the destination's upper lanes are zeroed, whether the
written register is the one the instruction names, and whether any flag or
memory effect was invented or lost. That is the class every bug in this program
has actually belonged to.

## Starting states

`--profile-set` selects the register/flag contexts a sweep starts from. The
default is the shipping three (`pointers`, `mixed`, `values`) and the gate's
coverage floors are counts over them, so **adding one to the default set would
inflate every recorded number without checking a single new word.** The others
are for hunting:

| set | contexts |
|---|---|
| `default` | pointers, mixed, values — NZCV in {0000, 1010, 1111} |
| `adversarial` | corner values (`0`/`1`/`-1`/`MIN`/`MAX`), `sp` at the top of scratch, `sp` sixteen bytes below the 64-bit wrap |
| `flags16` | one profile per NZCV setting — the whole domain of a condition code |
| `fp` | IEEE specials in the V file: `±0`, `±inf`, quiet and signalling NaN, both subnormal edges, the rounding boundaries |

## Reproducibility

The populations are pure functions of the tier (verified identical at 3, 8 and
11 workers), and each run prints a digest the gate checks. Mismatch counts,
opcode counts and family sets are exactly reproducible.

Two numbers are not, and both were learned from a false FAIL.

`compared` jitters by a word or two against `platform_register_x18`, because
whether the OS has already reset x18 in a given worker decides whether a word
that *reads* x18 is comparable.

`compared` also jitters against **`native_timeout`**, which is the only
exclusion that is not a function of the word: a fault is decided by the
candidate, a timeout by how many other processes wanted the core inside the
alarm window. A fast-tier run during a stage-1 rustc rebuild reported coverage
47300 against a floor of 47320 recorded on an idle host — twenty words, all
timeouts, formerly counted in `native fault / timeout` where nothing
distinguished them. **A gate that fails because somebody started a build is a
gate people learn to re-run instead of read.**

Every other exclusion is deterministic in (word, profile), so the gate's
coverage floor is the **sum** `compared + x18 + timeout` — exact — rather than a
tolerance on `compared`, which would have hidden the same amount of real loss.
`native_timeout` additionally carries its own ceiling, so a candidate class that
has genuinely started hanging still fails loudly instead of dissolving into the
sum.

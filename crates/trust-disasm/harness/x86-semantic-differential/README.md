# The x86-64 semantic differential

```sh
softwareupdate --install-rosetta --agree-to-license   # once, Apple silicon
./run.sh              # corpus + sweep + non-vacuity battery
./run.sh --random     # + a 20k random tier
```

**The third harness, and the one section A0 of `native-semantic` asked for.**
Until now the x86-64 model had a DECODE differential only (against LLVM); of the
sixteen 2026-08-18 defects that comparison could catch eight. Shift-count
masking and the shift flags needed something that EXECUTES. This executes.

**The oracle is Rosetta 2, not silicon.** This host has no x86-64 CPU (measured:
an `-arch x86_64` Mach-O will not start before `--install-rosetta`). Rosetta is
Apple's translator — an INDEPENDENT second implementation of x86-64, unrelated
to our model and to LLVM, with hardware TSO and exact scalar semantics as its
fidelity contract. Strictly stronger than the decode differential (it judges
values, flags, memory); strictly weaker than hardware (a bug Rosetta shares with
our model is invisible). The full normative blind-spot inventory — PF/AF not
compared, no vector/x87 state, generated coverage, one instruction per slot — is
the header of `src/main.rs`.

**What it found and drove to a fix** (nine model/decoder defects the decode
differential and even the AArch64 semantic differential could never see):
push/pop operand-size width; the ARM-shaped `Condition` enum turning `ja` into
"taken iff CF"; IMUL's CF/OF (asserted false, the wrong direction); the shift
no-op case (count 0 leaves flags UNCHANGED); the `operand_size` width gap across
the arithmetic/unary/shift immediate-to-memory groups (the rest of the `movb`
family); `pop rsp` ordering; and — all fail-closed, a verifying compiler must
not model an instruction the CPU traps on — illegal `LOCK`, unmodeled segment /
address-size overrides, implementation-defined `63` without REX.W, and illegal
`REP`/`REPNE`.

`baseline.json` records per-family mismatch COUNTS. corpus and sweep are the
gated tiers (0). random carries an adjudicated known-open set: the `0f 1e`
reserved encoding (SDM says NOP, LLVM says unknown, Rosetta #UDs — three
oracles) and corner-address memory faults.

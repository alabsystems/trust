# The x86-64 decode differential

```sh
./run.sh              # corpus + sweep + non-vacuity battery   (~20 s)
./run.sh --random     # + a 20k random-byte tier
```

**Why this exists.** The two harnesses beside it are AArch64 only — every
antecedent in them names `decode_aarch64` and `Aarch64Semantics`. Until
2026-08-18 the x86-64 half of `trust-disasm` was checked by unit tests alone,
that is, against expectations a human wrote down. An audit then found sixteen
defects in a day, five of them wrong ADDRESSES coexisting in one file, and two
checked-in tests were asserting two of the bugs as correct.

**What it is, and is not.** The AArch64 harnesses execute candidate words on the
CPU. This one cannot: measured on this host, an `-arch x86_64` Mach-O builds but
will not run (`bad CPU type in executable`) and Rosetta's `oahd` is not running.
So the oracle is LLVM's disassembler — `clang` to assemble, `objdump -d` to read
back — and the consequent is *agrees with an independent disassembler*, not
*agrees with the hardware*. Two decoders can be wrong together. It is a
differential, never an oracle unqualified.

It is a **decode** differential: lengths, effective-address terms (or the
resolved absolute address), and register operands. Nothing about EFFECTS. Of the
sixteen defects it would have caught the eight decode-level ones and missed
shift-count masking and the shift flags.

The full blind-spot inventory is normative and lives at the top of `src/main.rs`
— **if a limitation is not listed there, this harness is claiming to cover it.**

**It found a defect on its first run.** `decode_modrm_rm_reg` built its register
operand with `gpr(…, op_width)` rather than `gpr8`, so `mov r/m8, r8` rendered
register 5 as `bpl` instead of `ch` — the AH/SPL confusion again, at a fourth
site that three rounds of hand-auditing had missed. The fix routes every
variable-width construction through `gpr_sized`.

`baseline.json` records per-family mismatch COUNTS, not just names: a count is a
ceiling, and growth is a regression. That is deliberate — the sibling
`native-semantic` baseline recorded names only, and a regression inside an
already-open family passed its gate silently.

# Runtime ledger — proven-overflow-check elision

Regression coverage for the moonshot's "at-runtime" ledger, increment 1. When the
verifier **kernel-certifies** (clean CIC re-check) the no-overflow VC of an
arithmetic Add/Sub/Mul, the pass rewrites its overflow `Assert` to a `Goto`.

> **This battery pins a MIR rewrite, not a product benefit. Do not cite it as
> evidence of a better binary.** (Retraction, 2026-07-25.) It compiles only with
> `--emit=metadata` / `--emit=mir` and at no optimization level, so it never
> observes an object file. Measured at `-Copt-level=3`, the emitted code for
> *these exact fixtures* is **identical** to the vanilla lane — LLVM's own
> dominance and correlated-value analysis already removes every one of these
> checks unaided. The prior framing ("a superior binary … a binary Rust cannot
> produce") was not supported by anything this directory tests, and is withdrawn.
>
> Two things are separately true and worth stating precisely:
> * At `-Copt-level=0` the elision is visible (80 vs 267 asm lines, 0 vs 6 panic
>   refs on the fixture set) — real, but nobody ships `-O0`.
> * The differentiated win is a bound LLVM **cannot** see because it lives in a
>   caller contract. `fn inc(x: u32) -> u32 requires x < 1000 { x + 1 }` compiles
>   at `-O3` to `add w0, w0, #1 ; ret` (11 asm lines, no frame, no unwind tables)
>   against vanilla's 75 lines with `.cfi_personality`, an LSDA and a panic path;
>   over 30 such functions, 240 vs 1440 bytes of `__text`. An object-file lane
>   pinning *that* class is what would support a product claim. It does not exist
>   yet.
>
> Honesty constraint: "a binary Rust cannot produce" is literally false — vanilla
> can use `-C overflow-checks=off`, `wrapping_*`, or `get_unchecked`. The
> defensible claim is *better code from the same safe source under the same
> checked semantics*.
>
> See `reports/audit-2026-07-25-contract-loss-under-inlining.md`.

Design: the internal 2026-07-22 runtime-ledger overflow-elision design note.
Seam: `elide_kernel_certified_checks` in `compiler/rustc_mir_transform/src/trust_verify.rs`.
It has no opt-in switch — it runs wherever verification runs, and needs
`-C overflow-checks=on` for an `Assert` to exist at all.

## Run

```bash
./x.py build --stage 2
TRUST_SEED_STAIRCASE=1 python3 tests/trust-elide/elide_regression.py
```

## What it pins

| property | fixture | assertion |
|---|---|---|
| **proven elides** | `if x>10 {x-10}`, `if x!=0 {x-1}`, `a as u16 + 1`, `if x<1000 {x+1}` | the kernel-certified overflow `Assert` becomes a `Goto` (`elided=1`) |
| **unsafe rejected** | `a + b` (u32) | verification FAILS (`exit=1`), never codegen'd, never elided |
| **vanilla baseline** | all | under `-Ztrust-verify=off`, `elided=0` and the `Assert` survives |
| **value-preserving** | all | the `*WithOverflow` rvalue is retained (only the panic edge drops) |

## Soundness

Elision is fail-closed by construction: a check is elided ONLY for a
`ResultProofAuthority::KernelCertified` row that re-passes `matches_row` +
`matches_compiler_result`, joined to its MIR block by the authority's own
formula-inclusive `canonical_vc` string (never a span — coalescing would
over-license), with a live-terminator re-confirm. Any weaker authority, ambiguous
origin (a canonical shared by ≥2 blocks), kind mismatch, or shifted terminator ⇒
the check is kept. So a proven-but-not-kernel-certified op (e.g. interval-discharged
to a plain `Proved`) also keeps its check — only genuine per-op kernel proofs elide.

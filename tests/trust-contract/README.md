# Contract enforcement across the optimization pipeline

A `requires` clause is a **caller-side** obligation. Trust derives it from `Call`
terminators, so anything that removes a call before the verifier looks removes the
obligation with it. This directory pins that it does not.

## Run

```bash
./x.py build --stage 2
sh tests/trust-contract/contract_inline_repro.sh
```

Exits non-zero if a caller contract was dropped. Skips (exit 0) with no stage2
toolchain.

> **Status, 2026-09-30.** Measured on stage2 `13962dbde` (July): `-O3` accepted the
> violating caller, the A2 binary returned `0` where vanilla must panic, and the
> cross-crate consumer was accepted. The plain `-Copt-level` rows went green with
> the -O parity ruling R1 (2026-09-25), which runs the `-O0` MIR pipeline in a
> verifying session at every opt-level, so those rows no longer reach the MIR
> inliner at all: the defect was masked, not fixed. The `[explicit inliner]` rows
> (`-Zmir-opt-level=2`, `-Zinline-mir=yes`) ask for the inliner and were RED on a
> stage 1 of `fbc6068e3` (every one accepted; the A2 binary returned `0`). The rule
> that keeps a call to a `requires`-carrying callee in a verifying session
> (`compiler/rustc_mir_transform/src/trust_verify/requires_callee_inlining.rs`)
> is prepared, not built: they are predicted green with it. Do not "fix" a red row
> by weakening an assertion.
>
> A non-zero exit is deliberately **not** accepted as proof of rejection. The
> first version of this script reported all-green because a renamed flag made every
> invocation fail with `unknown unstable option`, which it read as "rejected". A
> battery that cannot tell "the verifier refused this program" from "the compiler
> refused my flags" will certify a live soundness defect as fixed.

## What it pins

| property | fixture | assertion |
|---|---|---|
| **`requires` is opt-level invariant** | `identity(x) requires x < 1000`, called with `u32::MAX` | rejected at `-O0`, `-O1` and `-O3` alike, and with an explicit inliner (`-Copt-level=3 -Zmir-opt-level=2`, `-Zinline-mir=yes`) |
| **inlining is the isolating variable** | same fixture | `-Zinline-mir=no` and `#[inline(never)]` reject — so a divergence at `-O3` is inlining, not contract transport |
| **`ensures` stays callee-side** | `wrong(x) ensures result > x { x }` | rejected at every level (it never depended on a surviving call) |
| **elision cannot outlive its licence** | `inc(x) requires x < 1000 { x + 1 }` | rejected at `-O3` and with an explicit inliner; and if accepted, the linked binary must not return a wrapped value |
| **contracts bind downstream** | `#[inline]` contract in an rlib + violating consumer | the downstream crate is rejected, with and without an explicit inliner |

## Why this exists

Two defects, both measured 2026-07-24 on stage2 `5a5d79119`:

- **A1** — at `-Copt-level=3` a violating caller compiled with **zero errors**;
  at `-O0` and under `-Zinline-mir=no` the same source was correctly rejected.
  Caller obligations are built from `Call` terminators surviving into *final
  optimized* MIR (`trust_verify.rs:13033` `body_has_call_terminator`, `:13051`
  early-out), while MIR inlining runs at `lib.rs:790`/`:793` and `TrustVerify`
  runs last at `:858`.
- **A2** — with proof-directed check elision on top, the same loss produced
  **wrong code**: the program linked and printed `0` where vanilla Rust with
  `-C overflow-checks=on` must panic. The inliner reads callees through
  `tcx.instance_mir` (`inline.rs:635`, `:1389`), which for a local def *is*
  `optimized_mir` — the body `TrustVerify` already erased.

The load-bearing lesson: **"TrustVerify is the last pass" is a per-body property.**
It does not survive interprocedural inlining, because the protected body becomes an
input to other bodies' pipelines and is serialized into crate metadata.

Full analysis, including the consumer table and why CTFE/promotion are unaffected:
the internal 2026-07-25 audit of contract loss under inlining.

## Scope note

This is a shell-level differential battery on purpose: the defect is a *divergence
between configurations of the same source*, which a single-configuration `ui` test
cannot express. The durable form of this check is a differential oracle over the
whole contract corpus (`-O0` vs `-O3`, fail on any verdict divergence) — that would
have caught both defects the day they landed and is the cheapest defence against
the next one.

# Provability instruments — Program 3, Phase A

Two instruments, both read-only, both classifying on the per-obligation JSON
transport rather than on exit codes.

Charter: the internal 2026-07-25 Program 3 prove-rate plan

```bash
./x.py build --stage 2
python3 tests/trust-provability/minimal_pairs.py
python3 tests/trust-provability/census.py --files 'tests/ui/trust/*.rs' --out reports/provability-census-<date>
```

## `minimal_pairs.py` — the defect-finding instrument

Two functions differing in exactly **one** syntactic element, compiled together,
verdicts compared. Both currently-known provability defects were found this way,
and a minimal pair is the cheapest possible evidence that a difference is real
rather than incidental.

Frozen against `EXPECTED.json`. A row moving **toward** `proved` is progress —
rerun with `--update` and say so in the commit. A row moving away is a
regression.

## `census.py` — the cause taxonomy

The prove rate is known: **1222 of 5379 obligations (22.7%)** on Trust's own
`trust-types` (internal report `rung3-trustc-self-verifies-trust-types.md:20`).
The *split by cause* is not, and each cause wants a different fix, so this exists
before any fix does.

| bucket | meaning | the fix it implies |
|---|---|---|
| **(a) incompleteness** | the prover could not establish a true fact | stronger domains / better encodings |
| **(b) authority-gap** | a solver **did** establish it, but no exact kernel/native authority could be minted | a checkable derivation from the domain — Phase D |
| **(c) unmodeled** | the construct could not be modeled at all | extraction / lowering coverage |
| **(d) no-specification** | nothing was authored to prove | **not a defect** — reported apart, never folded into a denominator |
| *refuted* | the verifier claims a counterexample | correct if the code is wrong; **the wall** if it is not |

**Bucket (b) is the one that is easy to miss and expensive to leave.** Those rows
are provable *today* — the solver said so — and they are being discarded. They
also can never license an optimization, because erasure requires
`KernelCertified`, so every one of them is a proof that was paid for and thrown
away.

## `policy_directions.py` — the ruling's three directions

Pins all three dispositions the completeness-gap ruling requires
(`docs/design/2026-07-25-completeness-gap-policy-ruling.md`, §"What must be true
before any code lands", item 3), over `directions/`:

| fixture | direction | default | certify |
|---|---|---|---|
| `gap_with_fallback.rs` | gap WITH a runtime fallback | builds | rejected |
| `refutation.rs` | genuine refutation | rejected | rejected |
| `nofallback.rs` | unproved row with NO fallback | rejected | rejected |

The third is the load-bearing one — it is the only thing separating policy B from
"accept anything unproved" — and it is the one C.7 never measured.

**This battery is the exception to the rule below, which is why it is the most
carefully guarded file here.** For the other instruments the exit code is noise;
here it *is* the measurement, because "does the build succeed?" is the entire
question. So it screens every run for the compiler refusing its *flags* and for
an ICE before reading any exit code as a verdict.

It also guards against passing for the wrong reason. `nofallback.rs` must produce
an actual `postcond` row, and that row's outcome must NOT be a refutation — a
false postcondition would be refuted, which already fails under `refutation.rs`,
so the case would silently become a duplicate that pins nothing. Both guards were
falsified before being trusted: inverting either expectation makes the battery
exit 1.

Measured at stage2 `2d87b63cc`: all three hold.

## Why exit codes are never the verdict

The scripts refuse to infer a verdict from a process exit code, and report a
`HARNESS` error instead when the compiler rejects their own flags.
(`policy_directions.py` must read exit codes — see its own section above for how
it screens them first.)

This is not hypothetical. A sibling battery in this repo once reported
**all-green while the defect it existed to catch was wide open**: a flag rename
(`-Zno-trust-verify` → `-Ztrust-verify`) made every invocation exit non-zero with
`unknown unstable option`, and the harness read "non-zero" as "the verifier
rejected it". See [`tests/trust-contract/README.md`](../trust-contract/README.md).

A battery that cannot distinguish *"the verifier refused this program"* from
*"the compiler refused my flags"* will certify a live soundness defect as fixed.

## Provenance rule

Every figure carries the `trustc` stamp **and** the host triple; both scripts
print them. These numbers become the ratchet baselines in the completeness-gap
ruling (the internal 2026-07-25 completeness-gap policy ruling),
so an unstamped baseline is worse than none. Build and measure at one commit —
`trustc`'s version stamp embeds HEAD.

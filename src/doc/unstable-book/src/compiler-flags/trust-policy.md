# Trust verification policy

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-policy=strict|advisory|memory-safe` selects how an *active*
verification run enforces its own verdicts. It never turns verification on or
off — that is `-Z trust-verify` — and it never changes which obligations are
generated or which evidence is produced. Every setting runs the same
artifact-backed verifier and reports the same obligation table.

The three settings are one option because they are mutually exclusive answers to
one question. Spelled as separate switches they were an enum with a
representable invalid state, and the pair had to be rejected by a hand-written
cross-check downstream of the callers that could construct it.

## `strict` (default)

Fail-closed. Every in-scope outcome must be statically proved: failed, unknown,
timed-out, runtime-checked, unsupported, and skipped outcomes all fail the
compilation, and a forced counterexample escalates. `#[trust::skip]` is rejected
in this lane.

## `advisory`

Verification and evidence production stay active, but nothing in the verify pass
is a hard error: unproved obligations are reported instead of failing the build,
and forced-counterexample escalation is suppressed. `#[trust::skip]` becomes an
`assumption:user-opt-out` structured row rather than disappearing. This is the
lane `targo trust --allow-l0-gaps` selects, and the only one that can retain a
declared reachable panic as `contract-panic:*` conditional evidence.

`-Z trust-dump=mir-only:<dir>` requires this policy, because skipping proof
dispatch entirely cannot produce a strict verdict.

## `memory-safe`

A narrow demotion, not a general relaxation. Reachable Rust panic refutations and
supported capability gaps become explicit assumption rows **only** in functions
that contain no source or inlined `unsafe`. Undefined behavior, hardened
boundary, contract, functional, and unmarked failures stay strict everywhere.

Because the demotion is conditioned on the absence of `unsafe` in the function
itself, it is not a way to accept an unproved unsafe operation: any function
carrying one is verified under the strict rules regardless of this setting.

## Evidence

The policy is a dependency-tracked compiler option, so a report's policy source
is authenticated by the compilation identity rather than by ambient process
state; the former `TRUST_VERIFY_POLICY`-style environment inputs are rejected.
No setting other than `strict` may be presented as proof-complete evidence.

# `cmp-mono-select-2026-07-16` provenance

This directory is a historical, non-authoritative W16 harvest from a probe
crate that called `cmp::min`, `cmp::max`, and `clamp` at concrete integer types.
It contains 22 monomorphic MIR observations, including local probe wrappers
that the final hardened hook deliberately no longer emits.

`results.tsv` is a strict three-column manifest:

1. SHA-256 of the exact JSON dump bytes;
2. the dump's `def_path` encoded as a JSON string, so tabs and escapes cannot
   change TSV column boundaries;
3. the observed cluster tag.

Run `./regenerate-results.sh` to validate all JSON records and rebuild the
manifest with a freshly executed `ff-gate-diagnose-2026-07-10`. The script
requires the exact closed identity set and current split: 16
`FULLY_FAITHFUL`, six `SHAPE_GAP`. The manifest records analyzer observations;
it is not a proof ledger, and the analyzer executable's identity is not
retained after the run.

Seven local probe records originally carried the generating machine's absolute
scratch path. That one exact prefix was canonicalized to
`SOURCE/monocmp.rs`; no semantic field or other span component was rewritten.
`results.tsv` was regenerated after normalization, so its SHA-256 values bind
the portable committed bytes.

## Findings

The concrete `Ord::min`/`max` bodies select over a total-but-uninterpreted
comparison sentinel. The exact scalar sentinel-select lane now kernel-checks
the shape-only statement “the total Boolean selects one of the two integer
arguments”; it deliberately carries no relation between that Boolean and
numeric ordering. The six exact leaves and ten forwarding bodies therefore
classify `FULLY_FAITHFUL` relative to the documented Trust-IR
uninterpreted-call model, not as proofs of numeric minimum/maximum semantics.
Forwarders certify only through the normal certified-callee registry; their
mere presence in this corpus grants no credit. This closes
`W-SELECT-OVER-CALL` only at that explicitly scoped shape-faithful tier.

Some `PartialOrd::lt` and `Ord::clamp` observations have an empty body with an
undefined return place after extraction. They remain rejected as
`W-DEREF-CMP-LEAF`/`W-NESTED-SELECT`. Treating an undefined body as a proof
would be unsound.

## Authority boundary

The historical run did not retain the exact generator-binary digest, and the
22-body universe predates the final hook's local-instance and contract-bundle
exclusions. These files are useful regression inputs and observational evidence
only. The files and manifest must not be used by themselves to discharge a
verification condition or mint a verdict; classification requires the current
recognizer, safety gates, certified-callee ordering, and kernel checker.

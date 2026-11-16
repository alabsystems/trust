# Original unsigned-bound compiler questions

These public contracts and requested obligations are unchanged records from
the retained `trust-intbound` compiler capture. Native programs are the same
six original inputs already checked in under the selected `trust-wp` component's
`tests/body_contract/fixtures/u64_calls/`; the consumer tests reuse those files.

The five typed questions exercise default MC-to-WP routing when MC cannot
summarize a retained local callee. MC contributes no proof or premises; WP must
compose the actual program and produce fresh checked evidence for the exact
public claim. Mutated claims and stale program evidence remain rejected.

`signed_min_magnitude` stays in the sample. Its original native replay record
contains only a source location, without a typed predicate or bindings. A wide
public integer constant does not authorize reconstructing that missing input.

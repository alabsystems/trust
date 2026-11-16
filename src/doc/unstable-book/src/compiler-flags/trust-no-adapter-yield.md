# `trust-no-adapter-yield`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-no-adapter-yield` (default: off) disables the `ADAPTER_YIELD` modeled
fact.

With the fact enabled, a local closure handed by value, exactly once, to a core
iterator adapter (`Iterator::{all, any, position, find, filter, map, for_each,
fold}`) over a receiver the compiler traced to `<[T]>::windows(k)`,
`chunks_exact(k)`, `chunks(k)` (constant `k >= 1`), or a constant-bounded
integer `Range` (optionally under `rev`/`step_by`) is verified assuming its item
parameter only ever holds an item that receiver yields: a sub-slice of length
`k` (`[1, k]` for `chunks`), or an integer in `start..end`. That is std's
documented contract; std is not re-verified, so the fact is recorded in
`docs/TCB.md` ("Modeled-fact axioms") and every function relying on it names it
in a `note:` and in the JSON `modeled_facts` field.

This flag is the negative control for that lane. It installs no premise at all,
so running with and without it is a cheap A/B on whether a verdict depended on
the fact. Setting it can only *lose* proofs, never gain them. It is
dependency-tracked because it changes which obligations resolve.

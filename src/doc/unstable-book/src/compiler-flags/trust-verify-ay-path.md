# `trust-verify-ay-path`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-ay-path=<path>` uses the executable at this non-empty path as
the AY verification solver instead of the one discovered in the sysroot.

The **location** is untracked; the solver's **contents** are tracked. Before any
dependency hash is observed, `rustc_interface` snapshots and hashes the exact
bytes at this path and records that content identity in the tracked top-level
`trust_solver_content_fingerprint`. Tracking the path as well would rotate
crate and incremental hashes whenever identical solver bytes merely moved, which
is churn without a corresponding change in what was proved.

An empty or whitespace-only path is rejected, including when a compiler
embedding injects it through a callback.

The retired `AY_PATH` environment variable is not a fallback: a Trust-semantics
compilation is a fatal error if it is set, because a solver selected by ambient
process state is a proof input nothing can authenticate.

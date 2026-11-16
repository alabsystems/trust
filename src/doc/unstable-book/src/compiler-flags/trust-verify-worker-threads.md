# `trust-verify-worker-threads`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-worker-threads=<N>` sets how many worker threads the verifier
may use, from `0` through `256`. `1` is serial dispatch. The default is `0`,
which means no cap: no sized pool is created and the verifier's engine batches
run in parallel on the default pool.

A value above `256` is rejected, including when a compiler embedding injects it
through a callback rather than the command line.

This is a throughput knob only. It cannot change a verdict: the same obligation
set is generated and each obligation is judged by the same backend regardless of
how many threads carry the work.

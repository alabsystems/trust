# `trust-verify-function-budget-steps`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-function-budget-steps=<N>` sets the per-function
**preprocessing step** budget. The default is `64000000`; `0` disables it.

Every instrumented pre-dispatch loop iteration decrements the counter, and
reaching zero fails that function closed — never `Proved`.

This exists alongside `-Z trust-verify-function-budget-ms` because the two bound
different things and only one of them is a proof:

- The step budget is a strictly decreasing natural number, so it is a *provable*
  termination bound. It holds even with the clock disabled, and it does not
  depend on how fast the machine is.
- The wall-clock budget caps super-polynomial work *per step*, which a step count
  cannot see.

Neither replaces the other, and neither is the per-obligation solver timeout
(`-Z trust-verify-timeout-ms`). When a function exhausts either budget the
compiler names both limits in the diagnostic.

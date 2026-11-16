# `trust-verify-function-budget-steps`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-function-budget-steps=<N>` sets the per-function
**preprocessing step** budget. The default is `64000000`. `N` must be positive:
`0` is refused, because the step budget has no off switch.

Every instrumented pre-dispatch loop iteration decrements the counter, and
reaching zero fails that function closed — never `Proved`.

This exists alongside `-Z trust-verify-function-budget-ms` because the two bound
different things and only one of them is a proof:

- The step budget is a strictly decreasing natural number, so it is a *provable*
  termination bound. It holds even with the clock disabled, and it does not
  depend on how fast the machine is: a function it stops is stopped at the same
  step on every host, and the row says so (stop cause `steps`).
- The wall-clock budget caps super-polynomial work *per step*, which a step count
  cannot see. A function it stops depends on machine speed and load, and the row
  says so (stop cause `wall-backstop`).

Without the step budget only the clock would bound preprocessing, and a clock
stop is not reproducible; that is why `0` no longer disables it. The default is a
seal constant, not a `[trust]` setting: `targo trust` does not pass this option,
so every run takes the seal's `64000000`.

Neither replaces the other, and neither is the per-obligation solver bound
(`-Z trust-verify-effort`, with `-Z trust-verify-timeout-ms` behind it). When
a function exhausts either budget the compiler names both limits in the
diagnostic.

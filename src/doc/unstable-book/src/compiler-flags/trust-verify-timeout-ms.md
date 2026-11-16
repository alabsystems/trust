# `trust-verify-timeout-ms`

The `-Z trust-verify-timeout-ms=<milliseconds>` option sets the positive,
tracked wall-clock timeout for each solver obligation. The compiler's own
default is `20000` ms; `targo trust` derives `5000` ms at the built-in backstop
(`[trust] backstop`, per mille of `5000` ms). The compiler threads this value through the VC router, MIR-level
BMC, the in-process AY bridge queries and the native CHC/PDR engine. The retired
MIR TrustWP path is an optional diagnostic invariant probe and never a proof
route.

On the router's AY lanes every solve also runs on its own size-scaled count
(`-Z trust-verify-effort`), at most 100,000 conflicts per SAT solve, about 1.6 s
of solver CPU on an idle host. The count usually ends an undecided search
before this clock, but not always: a `check-sat` can run several SAT solves,
and AY's residual clock (its SAT solver's wall-capped inprocessing and
lookahead outside the bit-blast solves) moves where the count stops a search,
so a query that spends its time outside conflicts can reach this clock first. The native CHC/PDR engine has no count yet, so
there this clock is still the bound. Either way a solve the clock ends is
recorded with stop cause `wall-backstop`, and the unit is not reproducible. The
value does not rise until every lane it bounds has a count in front of it.

Zero is rejected. Use `-Z trust-verify-function-budget-ms=0` only when the
separate cooperative function-wide budget must be disabled; it does not disable
this per-obligation timeout.

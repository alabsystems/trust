# `trust-verify-timeout-ms`

The `-Z trust-verify-timeout-ms=<milliseconds>` option sets the positive,
tracked timeout for each solver obligation. The default is `5000` ms, matching
Targo and `trust.toml`. The compiler threads this value through the VC router,
MIR-level BMC and in-process AY bridge queries. The retired MIR TrustWP path is
an optional diagnostic invariant probe and never a proof route.

Zero is rejected. Use `-Z trust-verify-function-budget-ms=0` only when the
separate cooperative function-wide budget must be disabled; it does not disable
this per-obligation timeout.

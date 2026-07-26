# `trust-verify-function-budget-ms`

The `-Z trust-verify-function-budget-ms=<milliseconds>` option sets a tracked,
cooperative budget for one function's verification work. The default is
`120000` ms; `0` disables this function-wide budget.

Once the deadline expires, the compiler starts no new proof query and rejects a
proof returned late. Full verification therefore fails closed on exhaustion.
Because verification preprocessing runs in-process, this is a cooperative
deadline rather than an asynchronous mechanism that can unwind arbitrary Rust
code; individual solver calls remain bounded by
`-Z trust-verify-timeout-ms`.

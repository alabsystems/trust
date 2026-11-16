# `trust-verify-function-budget-ms`

The `-Z trust-verify-function-budget-ms=<milliseconds>` option sets a tracked,
cooperative budget for one function's verification work. The default is
`120000` ms, the value `targo trust` passes at the built-in backstop; `0`
disables this function-wide budget.

Once the deadline expires, the compiler starts no new proof query and rejects a
proof returned late. Full verification therefore fails closed on exhaustion.
Because verification preprocessing runs in-process, this is a cooperative
deadline rather than an asynchronous mechanism that can unwind arbitrary Rust
code; individual solver calls remain bounded by `-Z trust-verify-effort` and
`-Z trust-verify-timeout-ms`.

Two counts stand in front of this clock: the step budget
(`-Z trust-verify-function-budget-steps`) bounds preprocessing, and each AY
query's own effort count (`-Z trust-verify-effort`) bounds that query's solver
work. The native CHC/PDR engine, kernel certification and the structural
promotions have no count yet, so for them this deadline is still the bound. A
function this clock stops is recorded with stop cause `wall-backstop`.

`targo trust` derives the value from `[trust] backstop` (per mille of
`120000` ms; `1000`, the built-in, passes `120000`).

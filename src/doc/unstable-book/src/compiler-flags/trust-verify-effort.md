# `trust-verify-effort`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-effort=<k>` sets the solver **effort scale**: SAT conflicts
per distinct query term. The default is `384`; the value must be from `1`
through `100000`.

Each AY query that goes through the verifier's router gets one count, scaled
to its size:

```text
effort = min(100000, max(1, k * size))
```

where `size` is the number of distinct terms (DAG nodes) of the assertions in
scope at that `check-sat`. The router's three AY ingress points send that count
as `(set-option :rlimit effort)` right before the `check-sat` it bounds: the
in-process program, the subprocess session (one per `check-sat`, sized over the
assertions the session holds at that point) and the one-shot script. A query
split into disjoint components gives each component its share of the count in
proportion to the component's size. S1 strict revalidation and the R1 harvest
re-check a query under its own count. AY stops each SAT solve at that count and
answers `unknown`, and the row's stop cause is `effort`: a search the count
stops ends at the same point on every host.

There is one count on those lanes. No per-function account sits on top of it:
two functions with the same obligation run it on the same budget, whatever
else either of them proves. The step budget
(`-Z trust-verify-function-budget-steps`) bounds preprocessing.

The ceiling `100000` is the flat per-query count this scale replaced, so no
query is given more search than before. It costs about 1.6 s of solver CPU on
an idle host, so a SAT solve its count stops has used about a third of the
built-in per-query clock (`-Z trust-verify-timeout-ms`, 5000 ms under
`targo trust`). It is below AY's own ground conflict allowance (400000 per SAT
solve), which an explicit `:rlimit` replaces, so the count only tightens AY's
bound. `0` is refused because AY reads `:rlimit 0` as unbounded solving.

What the count does not cover yet:

* It bounds each SAT solve inside a `check-sat`, not the whole check: a check
  that runs several SAT solves can spend more than `effort`.
* AY's own per-SAT-solve decision allowance stays in force under `:rlimit`, so
  a decision-heavy search can stop on it (also reported `effort`).
* AY's residual clock is its SAT solver's wall-capped restart inprocessing
  and lookahead, in every SAT solve but the BV/FP bit-blast ones. The
  strict-proof discharge, the eager-persistent split loop and the bit-blast
  solves run on counts under `:rlimit` (Trust's AY pin `da447f9a6`). The cap
  never ends a search, but it moves where the count stops one, and a query
  that spends its time outside conflicts can reach the per-query clock before
  its count; it stops `wall-backstop` and is not reproducible.
* The certification lanes' direct AY solves (clean-auto and the datatype
  no-confusion check in trust-certify) send no `:rlimit`: they run under AY's
  flat ground allowance and a 90 s clock read from `AY_DIRECT_SOLVE_TIMEOUT_MS`.
  The native CHC/PDR engine has no count either.

Each of these is a T2 dependency of the determinism plan; until it lands the
wall clocks (`-Z trust-verify-timeout-ms`, `-Z trust-verify-function-budget-ms`)
still end some searches, and every search a clock ends is recorded with stop
cause `wall-backstop`.

`targo trust` passes this value explicitly (`[trust] effort` at the workspace
root), and the budget profile id a report prints hashes it, so a report names
the count its rows ran under.

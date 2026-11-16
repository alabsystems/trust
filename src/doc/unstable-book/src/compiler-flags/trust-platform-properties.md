# `trust-platform-properties`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-platform-properties=<list>` (default: none) names the platform
protocol properties the platform-protocol pass checks
(`docs/design/2026-10-01-platform-protocols-as-trustc-errors.md`, Part 3).
The list is comma-separated; repeating the option adds to the set and never
removes from it.

| Property | Meaning |
|---|---|
| `fd-inherit` | No descriptor other than 0, 1 and 2 reaches the image a spawned child executes. |

**This trustc does not run the pass yet.** The controls are parsed, validated
and tracked (design PR 8); the pass itself is wired in a later landing (design
PRs 9 and 10). Setting the controls changes no diagnostic
and no emitted byte. Nothing prints a claim that a property was checked; a
gate that consumes platform verdicts must require the pass's summary row and
treat its absence as "did not run".

The checks are refutation-only: a property can fail the build with a replayed
counterexample, and it never proves anything. They apply only with
verification on (`-Z trust-verify=on`); under `-Z trust-verify=off` the pass
never runs. Under `-Z trust-policy=advisory` a refutation is still an error.

Every spelling outside the closed set is a hard error at option parsing,
including case and separator variants (`FD-INHERIT`, `fd_inherit`), an empty
value and an empty list element. `lock-release` and `fd-identity` are
properties the design defines that this trustc cannot check yet; asking for
one is also an error ("not supported by this trustc"), never an option that is
accepted and checks nothing.

The related controls, each refused outside its domain:

* `-Z trust-platform-unanalysed=warn|deny` (default `warn`): how a policy site
  the pass cannot analyse is reported. There is no `allow`: such a site is
  always named.
* `-Z trust-platform-budget=<states>` (default `1000000`): the exploration
  budget per derived model, in states, never in time. `0` is refused. A model
  that exceeds it leaves its sites unanalysed (`PC-BUDGET`).
* `-Z trust-platform-report=summary|verbose` (default `summary`): `verbose`
  adds a note per site that is not refuted.
* `-Z trust-platform-dump-facts=<path>`: test and measurement only; writes the
  host facts the pass gives the census, in the census sidecar grammar.

All five are dependency-tracked but do not enter the crate hash: the pass adds
diagnostics and never changes what is emitted.

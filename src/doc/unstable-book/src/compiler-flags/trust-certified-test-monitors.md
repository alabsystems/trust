# `trust-certified-test-monitors`

The tracking issue for this feature is internal to Trust.

------------------------

This is a reserved internal Targo phase-A fingerprint. Do not set it by hand.

`-Z trust-certified-test-monitors` marks a **non-`--test`** compilation unit as
a certified-monitor subject, so its tracked identity records that role. It
carries no independent authority of its own: without the nonce-bound phase-B
selector it would bypass the authenticated sysroot, startup, and native-link
closure that makes the monitor lane evidence-grade.

The compiler therefore rejects it unless all of the following hold:

- Full Trust verification is active. It cannot be combined with
  `-Z trust-verify=off`.
- The unit is *not* a native `--test` unit, which already enables certified
  monitors — the combination is redundant and rejected as such.
- The paired `-Z trust-targo-test-monitor` selector is present.
- `-Z trust-verify-session` and `-Z trust-verify-package-name` are both set and
  `-Z trust-verify-crate-role` is `primary` or `dependency` — that is, the unit
  is a session-scoped Targo harness-free test/bench root or a dependency-role
  execution unit selected by the resolved test graph.

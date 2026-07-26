# `trust-targo-test-monitor`

The tracking issue for this feature is internal to Trust.

------------------------

This is a reserved Targo-to-compiler protocol field, and **direct use is
rejected**.

`-Z trust-targo-test-monitor` is the per-unit session-consistency selector for
the certified-monitor test lane (`targo trust test`). It installs
kernel-certified clause monitors into a test binary. It never enables static
verification, and it does not authenticate a direct `trustc` caller.

The compiler refuses the option unless the surrounding conditions make it
evidence-grade:

- A matching `-Z trust-verify-session` must be present, and it must equal the
  value in the `TRUST_TARGO_TEST_MONITOR_SESSION` marker Targo sets. A padded,
  empty, or non-Unicode marker is rejected.
- `-C prefer-dynamic` is unavailable: an evidence-grade certified-monitor test
  needs a static Rust dependency closure.
- The sysroot must be the running compiler's own, recomputed rather than read
  out of the mutable `Options` field, so an embedding callback cannot redirect
  it. An explicit `--sysroot` is tolerated only when it canonicalizes to that
  same path (bootstrap and compiletest use that form).

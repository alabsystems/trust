# `trust-verify-output`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-verify-output=human|json|both` selects the verifier's transport
format. The default is `human`.

- `human` — diagnostics for a person reading a terminal.
- `json` — the structured transport `targo trust` parses to build a report.
- `both` — emit each row twice, once in each form. Useful when debugging a
  frontend against output you also want to read.

The option is dependency-tracked but does not enter the crate hash: it changes
what this compiler invocation prints, never what gets proved or what code is
emitted.

`targo trust` owns this setting and always requests the structured transport.
It is deliberately *not* settable through `TRUSTFLAGS`: authenticated coverage
parsing depends on the JSON transport, so a last-wins `human` override would
sever evidence collection and every run would fail closed with a confusing
transport error rather than an honest policy error.

The retired `TRUST_VERIFY_OUTPUT` environment variable is rejected outright — a
Trust-semantics compilation is a fatal error if it is set, rather than silently
running under untracked ambient state.

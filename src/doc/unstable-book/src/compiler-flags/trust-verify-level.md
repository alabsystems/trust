# `trust-verify-level`

The tracking issue for this feature is internal to Trust.

------------------------

Controls the proof depth used by Trust's native typed verification pipeline.
Rust and Lean/Clean source frontends target TrustIR directly. The
MIR routes currently retained by this option are compatibility proof routes,
not the long-term frontend boundary, and remain authoritative only until the
direct Rust route reaches exact semantic and proof-replay parity.

For public verifier usage, prefer `targo trust check` and
`targo trust check --format json`. Those commands are the supported front door;
this flag is the lower-level knob they pass through to the native Trust
compiler.

```text
trustc -Z trust-verify-level=0 your_file.rs
```

The currently supported levels are:

- `0`: safety obligations. This is the strongest public story today.
- `1`: contract and functional obligations. Present, but still settling.
- `2`: deeper or domain-specific obligations. Experimental.

The raw compiler default is `2`, matching the supported Targo frontend. An
explicit lower level narrows the obligation inventory; strict mode remains
fail-closed over every obligation selected at that level.

Higher-level docs often refer to these as `L0`, `L1`, and `L2`; `targo-trust`
maps those names to `0`, `1`, and `2` for the native compiler path.

Native/stage1 availability for this path is still tracked work rather than a
universally shipped guarantee, so do not treat direct `rustc -Z ...` use as the
normal first-run workflow.

The compiler rejects values outside `0`, `1`, and `2`. The level has no effect
in an explicit `-Z trust-verify=off` vanilla lane.

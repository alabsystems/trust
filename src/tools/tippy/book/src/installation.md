# Installation

Tippy ships as part of the Trust toolchain. A complete installation contains
the sibling executables `tippy`, `targo-tippy`, and `tippy-driver`; `targo`
discovers `targo-tippy` when you run `targo tippy`.

Verify the selected toolchain with:

```bash
tippy --version
targo tippy --version
tippy-driver --version
```

The Trust toolchain intentionally does not install `cargo-clippy` or
`clippy-driver` aliases. If those are the only names on `PATH`, a stock Rust
toolchain—not the selected Trust toolchain—is being used.

## From Source

From a Trust source checkout, build the component with
`./x.py build --stage 2 tippy`. See the repository's `INSTALL.md` for the full
standalone toolchain installation flow.

[Basics]: development/basics.md#install-from-source
[Usage]: usage.md

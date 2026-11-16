# Installation

## Install Trust Cargo

In this fork, the supported local baseline is the linked `trust` toolchain built
from this checkout. Build and link it first:

```console
CARGO_NET_OFFLINE=true ./x.py build --set llvm.ninja=false --stage 2 compiler/rustc library/std
rustup toolchain link trust ./build/host/stage2
rustup run trust cargo --version
```

Use `cargo +trust ...` or `rustup run trust cargo ...` for the current linked
baseline. Plain no-flags `cargo` is default-toolchain evidence only after
`rustup default trust` and a fresh `installed-default` gate.

## Build Cargo from Source

Cargo sources are part of this repository under `src/tools/cargo` and are built
as part of the Trust toolchain. Use [the Trust install guide][install-trust] for
the complete local flow.

[install-trust]: ../../../../../../../INSTALL.md

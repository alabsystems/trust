# Continuous Integration

It is recommended to run Tippy on CI with `-Dwarnings`, so that lint findings
prevent CI from passing. To enforce errors on warnings on all compiler
commands, not just `targo tippy`, you can set `RUSTFLAGS="-Dwarnings"`.

Always use `tippy`, `targo`, and `trustc` from the same Trust sysroot. Mixing a
stock Cargo/Clippy installation with a Trust compiler is unsupported and can
silently invalidate the toolchain evidence CI is meant to collect.

The `clippy::` lint namespace and configuration format remain compatible even
though the executable surface is Tippy-branded.

This chapter gives an overview of how to use Tippy on different popular CI
providers.

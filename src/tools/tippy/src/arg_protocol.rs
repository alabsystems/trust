// Targo owns the wire-format schema because its publishable `cargo` package
// must be self-contained. Tippy is `publish = false`, so it can safely include
// that canonical source without introducing a registry-release dependency or a
// second implementation that can drift.
include!("../../targo/src/cargo/util/tippy_arg_protocol.rs");

// Targo owns the wire-format schema because its publishable `targo` package
// must be self-contained. Tippy is `publish = false`, so it can safely include
// that canonical source without introducing a registry-release dependency or a
// second implementation that can drift.
include!("../../targo/crates/targo-core/src/util/tippy_arg_protocol.rs");

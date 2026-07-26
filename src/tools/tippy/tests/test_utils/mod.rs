#![allow(dead_code)] // see https://github.com/rust-lang/rust/issues/46379

use std::ffi::OsString;
use std::path::PathBuf;
use std::sync::LazyLock;

// Trust: `CARGO_BIN_EXE_*` exists only when cargo BUILDS this integration
// test target, so a compile-time `env!` made `cargo check` fail on a target
// it never links. Resolve through `option_env!` and fail at run time, where
// the variable is always present.
pub static CARGO_CLIPPY_PATH: LazyLock<PathBuf> = LazyLock::new(|| {
    PathBuf::from(
        option_env!("CARGO_BIN_EXE_cargo-clippy")
            .expect("CARGO_BIN_EXE_cargo-clippy is set whenever cargo builds this test"),
    )
});

pub const IS_RUSTC_TEST_SUITE: bool = option_env!("RUSTC_TEST_SUITE").is_some();

/// Reject any Trust semantic/evidence control in a direct driver invocation.
///
/// UI compiles need batteries-on verification out of the way, but they must not
/// ask for it: the driver enters rustc through the no-evidence boundary, and
/// that same policy both turns verification off by itself and fatally rejects
/// every `-Ztrust-*` option. Passing one is not redundant, it is fatal — and it
/// fails identically for all ~1000 UI tests, which reads as a broken harness
/// rather than a broken argument. Fail here instead, with the argument named.
pub fn reject_trust_frontend_controls(args: &[OsString]) {
    if let Some(forbidden) = args
        .iter()
        .find(|arg| arg.to_string_lossy().replace(' ', "").starts_with("-Ztrust-"))
    {
        panic!(
            "UI driver arguments carry the Trust control `{}`; the no-evidence lint frontend rejects it, \
             and it already runs with verification off",
            forbidden.to_string_lossy()
        );
    }
}

/// Supplemental bootstrap-shim context for Tippy's nested dependency Cargo
/// build. The caller supplies the compiler paths and sysroot; the all-units
/// opt-out here covers both target crates and host-side build scripts. The
/// outer `TEST_RUSTC` gate keeps this out of standalone runs.
pub fn bootstrap_dependency_builder_env(
    stage: &str,
    build_triple: &str,
    link_std: &str,
) -> [(OsString, Option<OsString>); 5] {
    [
        ("RUSTC_STAGE".into(), Some(stage.into())),
        ("CFG_COMPILER_BUILD_TRIPLE".into(), Some(build_triple.into())),
        ("RUSTC_LINK_STD_INTO_RUSTC_DRIVER".into(), Some(link_std.into())),
        ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY".into(), Some("1".into())),
        ("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY".into(), None),
    ]
}

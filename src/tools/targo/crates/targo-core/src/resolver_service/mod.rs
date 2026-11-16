//! The exact sealed Targo normal resolver under separately retained native ownership.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub const PROTOCOL_MARKER: [u8; 64] = trust_resource_controller::resolver::RESOLVER_PROTOCOL_MARKER;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use supported::{requested, run};
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub fn requested(args: &[std::ffi::OsString]) -> bool {
    args.first().is_some_and(|a| a == "--resource-resolver-v1")
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub fn run(
    _args: &[std::ffi::OsString],
    _lane: fn() -> crate::util::CargoResult<()>,
) -> crate::util::CargoResult<()> {
    anyhow::bail!("native resolver custody is unsupported on this platform")
}

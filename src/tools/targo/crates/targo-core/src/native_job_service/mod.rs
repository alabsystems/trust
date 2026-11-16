//! One actual admitted general native DAG. The startup consumes original
//! descriptions before config or threads; decoded plans remain equality DATA.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod comparison;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod comparison_attempt;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod context;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod land_attempt;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod verification;
pub const PROTOCOL_MARKER: [u8; 64] = trust_resource_controller::native_job::PROTOCOL_MARKER;
pub fn requested(args: &[std::ffi::OsString]) -> bool {
    args.first()
        .is_some_and(|arg| arg == trust_resource_controller::native_job::STARTUP_ARGUMENT)
}
pub fn run(
    args: &[std::ffi::OsString],
    bootstrap: crate::workload_service::Bootstrap,
    configure_lane: impl FnOnce() -> crate::util::CargoResult<()>,
) -> crate::util::CargoResult<()> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        supported::run(args, bootstrap, configure_lane)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = (args, bootstrap, configure_lane);
        anyhow::bail!("general native job is unsupported on this platform")
    }
}

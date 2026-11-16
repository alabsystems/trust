//! Native paired metadata runner façade. Unsupported Unix still follows the
//! original receipt owner's probe/refusal and final input-check path.

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) use supported::NativeMetadataRunner;

#[cfg(any(test, not(any(target_os = "linux", target_os = "macos"))))]
mod unsupported;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(crate) use unsupported::NativeMetadataRunner;

//! Concrete paired dependency resolver; unsupported Unix follows the same
//! ReceiptCheckedPair/probe/refusal and final original-input checks.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) use supported::NativeDependencyResolver;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(crate) struct NativeDependencyResolver;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
impl NativeDependencyResolver {
    pub(crate) fn new(_store: Option<std::path::PathBuf>) -> Self {
        Self
    }
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
impl trust_qualification::dependencies::DependencyResolver for NativeDependencyResolver {
    fn resolve(
        &mut self,
        _request: &trust_qualification::dependencies::ResolverRequest,
    ) -> trust_qualification::Result<trust_qualification::dependencies::ResolverCapture> {
        Err(trust_qualification::Refusal(
            "native resolver admission is unsupported on this platform".into(),
        ))
    }
}

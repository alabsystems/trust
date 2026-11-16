//! Targo executable facade. The reusable engine lives in `targo-core` so
//! checkout identity and packaged manuals cannot invalidate engine code.
pub use targo_core::*;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[doc(hidden)]
pub mod paired_compiler;

#[cfg(test)]
#[path = "../build_commit_info.rs"]
mod build_commit_info;

/// Bind the executable's validated build label before entering the engine.
/// This metadata is presentation only; it is never a proof or cache identity.
pub fn initialize_build_metadata() {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        let info = match (
            option_env!("CARGO_COMMIT_HASH"),
            option_env!("CARGO_COMMIT_SHORT_HASH"),
            option_env!("CARGO_COMMIT_DATE"),
        ) {
            (Some(hash), Some(short), Some(date)) => Some(CommitInfo {
                commit_hash: hash.to_owned(),
                short_commit_hash: short.to_owned(),
                commit_date: date.to_owned(),
            }),
            (None, None, None) => None,
            _ => panic!("incomplete validated Targo commit tuple"),
        };
        bind_build_commit(info).expect("inconsistent Targo executable build metadata");
    });
}

/// Return the executable label while keeping the engine's source identity separate.
pub fn version() -> VersionInfo {
    initialize_build_metadata();
    targo_core::version()
}

#[cfg(test)]
mod tests {
    #[test]
    fn executable_and_engine_report_the_same_bound_label() {
        let executable = super::version();
        let engine = targo_core::version();
        assert_eq!(executable.commit_info, engine.commit_info);
        assert_eq!(executable.version, engine.version);
        assert_eq!(executable.release_channel, engine.release_channel);
        assert_eq!(
            executable
                .commit_info
                .as_ref()
                .map(|c| c.commit_hash.as_str()),
            option_env!("CARGO_COMMIT_HASH")
        );
    }
}

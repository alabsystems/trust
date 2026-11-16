//! Code for representing cargo's release version number.

use std::fmt;

/// Information about the git repository where cargo was built from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitInfo {
    pub short_commit_hash: String,
    pub commit_hash: String,
    pub commit_date: String,
}

/// Cargo's version.
pub struct VersionInfo {
    /// Cargo's version, such as "1.57.0", "1.58.0-beta.1", "1.59.0-nightly", etc.
    pub version: String,
    /// The release channel we were built for (stable/beta/nightly/dev).
    ///
    /// `None` if not built via bootstrap.
    pub release_channel: Option<String>,
    /// Information about the Git repository we may have been built from.
    ///
    /// `None` if not built from a git repo.
    pub commit_info: Option<CommitInfo>,

    /// A descriptive string to be appended to version output.
    ///
    /// This is usually set by the bootstrap in rust-lang/rust
    /// via the `CFG_VER_DESCRIPTION` environment variable.
    /// Useful for showing vendor build information.
    /// For example,
    ///
    /// ```text
    /// cargo 1.85.0 (d73d2caf9 2024-12-31) (MyCustomBuild 1.85.0-3)
    /// ```
    pub description: Option<String>,
}

impl fmt::Display for VersionInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.version)?;

        if let Some(ref ci) = self.commit_info {
            write!(f, " ({} {})", ci.short_commit_hash, ci.commit_date)?;
        };

        if let Some(description) = self.description.as_ref().filter(|d| !d.is_empty()) {
            write!(f, " ({description})")?;
        };
        Ok(())
    }
}

/// Returns information about cargo's version.
pub fn version() -> VersionInfo {
    macro_rules! option_env_str {
        ($name:expr) => {
            option_env!($name).map(|s| s.to_string())
        };
    }

    // This is the version set in bootstrap, which we use to match rustc.
    let version = option_env_str!("CFG_RELEASE").unwrap_or_else(|| {
        // If cargo is not being built by bootstrap, then we just use the
        // version from cargo's own `Cargo.toml`.
        //
        // There are two versions at play here:
        //   - version of cargo-the-binary, which you see when you type `cargo --version`
        //   - version of cargo-the-library, which you download from crates.io for use
        //     in your packages.
        //
        // The library is permanently unstable, so it always has a 0 major
        // version. However, the CLI now reports a stable 1.x version
        // (starting in 1.26) which stays in sync with rustc's version.
        //
        // Coincidentally, the minor version for cargo-the-library is always
        // +1 of rustc's minor version (that is, `rustc 1.11.0` corresponds to
        // `cargo `0.12.0`). The versions always get bumped in lockstep, so
        // this should continue to hold.
        let minor = env!("CARGO_PKG_VERSION_MINOR").parse::<u8>().unwrap() - 1;
        let patch = env!("CARGO_PKG_VERSION_PATCH").parse::<u8>().unwrap();
        format!("1.{}.{}", minor, patch)
    });

    let release_channel = option_env_str!("CFG_RELEASE_CHANNEL");
    let commit_info = BUILD_COMMIT.get().cloned().flatten();
    let description = option_env_str!("CFG_VER_DESCRIPTION");

    VersionInfo {
        version,
        release_channel,
        commit_info,
        description,
    }
}

// Commit metadata is presentation supplied once by the executable, never an
// input to engine compilation or an authority for artifact/proof acceptance.
static BUILD_COMMIT: std::sync::OnceLock<Option<CommitInfo>> = std::sync::OnceLock::new();

pub fn bind_build_commit(info: Option<CommitInfo>) -> Result<(), &'static str> {
    bind_commit(&BUILD_COMMIT, info)
}

fn bind_commit(
    cell: &std::sync::OnceLock<Option<CommitInfo>>,
    info: Option<CommitInfo>,
) -> Result<(), &'static str> {
    let bound = cell.get_or_init(|| info.clone());
    if bound == &info {
        Ok(())
    } else {
        Err("Targo build commit metadata was already bound differently")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn build_commit_binding_is_immutable_and_idempotent() {
        let cell = std::sync::OnceLock::new();
        let info = Some(CommitInfo {
            commit_hash: "a".repeat(40),
            short_commit_hash: "aaaaaaaaa".into(),
            commit_date: "2026-11-03".into(),
        });
        assert!(bind_commit(&cell, info.clone()).is_ok());
        assert!(bind_commit(&cell, info.clone()).is_ok());
        assert!(bind_commit(&cell, None).is_err());
        assert_eq!(cell.get(), Some(&info));
    }
}

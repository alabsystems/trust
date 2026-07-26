use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};

use anyhow::Error;
use flate2::read::GzDecoder;
use tar::Archive;
use xz2::read::XzDecoder;

const DEFAULT_TARGET: &str = "x86_64-unknown-linux-gnu";

macro_rules! pkg_type {
    ( $($variant:ident = $component:literal $(; preview = true $(@$is_preview:tt)? )? $(; suffixes = [$($suffixes:literal),+] $(@$is_suffixed:tt)? )? ),+ $(,)? ) => {
        #[derive(Debug, Hash, Eq, PartialEq, Clone)]
        pub(crate) enum PkgType {
            $($variant $( $($is_suffixed)? { suffix: &'static str })?,)+
        }

        impl PkgType {
            pub(crate) fn is_preview(&self) -> bool {
                match self {
                    $( PkgType::$variant $($($is_suffixed)? { .. })? => false $( $($is_preview)? || true)?, )+
                }
            }

            /// First part of the tarball name. May include a suffix, if the package has one.
            pub(crate) fn tarball_component_name(&self) -> String {
                match self {
                    $( PkgType::$variant $($($is_suffixed)? { suffix })? => {
                        #[allow(unused_mut)]
                        let mut name = $component.to_owned();
                        $($($is_suffixed)?
                        name.push('-');
                        name.push_str(suffix);
                        )?
                        name
                    },)+
                }
            }

            pub(crate) fn all() -> Vec<PkgType> {
                let mut packages = vec![];
                $(
                    // Push the single variant
                    packages.push(PkgType::$variant $($($is_suffixed)? { suffix: "" })?);
                    // Macro hell, we have to remove the fake empty suffix if we actually have
                    // suffixes
                    $(
                        $($is_suffixed)?
                        packages.pop();
                    )?
                    // And now add the suffixes, if any
                    $(
                        $($is_suffixed)?
                        $(
                            packages.push(PkgType::$variant { suffix: $suffixes });
                        )+
                    )?
                )+
                packages
            }
        }
    }
}

pkg_type! {
    Rust = "trust",
    RustSrc = "trust-src",
    Rustc = "trustc",
    RustcDev = "trustc-dev",
    RustcDocs = "trustc-docs",
    ReproducibleArtifacts = "reproducible-artifacts",
    RustMingw = "trust-mingw",
    RustStd = "trust-std",
    Cargo = "targo", // Trust: produced frontend component is targo
    TCargoTrust = "targo-trust",
    HtmlDocs = "trust-docs",
    RustAnalysis = "trust-analysis",
    RustAnalyzer = "trust-analyzer"; preview = true,
    Clippy = "tippy"; preview = true, // Trust: produced linter component is tippy
    Rustfmt = "trustfmt"; preview = true,
    LlvmTools = "trust-llvm-tools"; preview = true,
    Miri = "trust-miri"; preview = true,
    JsonDocs = "trust-docs-json"; preview = true,
    LlvmBitcodeLinker = "llvm-bitcode-linker"; preview = true,
    Enzyme = "enzyme"; preview = true,
}

impl PkgType {
    /// Component name in the manifest. In particular, this includes the `-preview` suffix where appropriate.
    pub(crate) fn manifest_component_name(&self) -> String {
        if self.is_preview() {
            format!("{}-preview", self.tarball_component_name())
        } else {
            self.tarball_component_name()
        }
    }

    /// Whether this package has the same version as Rust itself, or has its own `version` and
    /// `git-commit-hash` files inside the tarball.
    fn should_use_rust_version(&self) -> bool {
        match self {
            PkgType::Cargo => false,
            PkgType::RustAnalyzer => false,
            PkgType::Clippy => false,
            PkgType::Rustfmt => false,
            PkgType::LlvmTools => false,
            PkgType::Miri => false,

            PkgType::Rust => true,
            PkgType::RustStd => true,
            PkgType::RustSrc => true,
            PkgType::Rustc => true,
            PkgType::JsonDocs => true,
            PkgType::HtmlDocs => true,
            PkgType::RustcDev => true,
            PkgType::RustcDocs => true,
            PkgType::ReproducibleArtifacts => true,
            PkgType::RustMingw => true,
            PkgType::RustAnalysis => true,
            PkgType::LlvmBitcodeLinker => true,
            PkgType::TCargoTrust => true,
            PkgType::Enzyme => true,
        }
    }

    pub(crate) fn targets(&self) -> &[&str] {
        use PkgType::*;

        use crate::{HOSTS, MINGW, TARGETS};

        match self {
            Rust => HOSTS, // doesn't matter in practice, but return something to avoid panicking
            Rustc => HOSTS,
            RustcDev => HOSTS,
            ReproducibleArtifacts => HOSTS,
            RustcDocs => HOSTS,
            Cargo => HOSTS,
            TCargoTrust => HOSTS,
            RustMingw => MINGW,
            RustStd => TARGETS,
            HtmlDocs => HOSTS,
            JsonDocs => HOSTS,
            RustSrc => &["*"],
            RustAnalyzer => HOSTS,
            Clippy => HOSTS,
            Miri => HOSTS,
            Rustfmt => HOSTS,
            RustAnalysis => TARGETS,
            LlvmTools => TARGETS,
            LlvmBitcodeLinker => HOSTS,
            Enzyme => HOSTS,
        }
    }

    /// Whether this package is target-independent or not.
    fn target_independent(&self) -> bool {
        *self == PkgType::RustSrc
    }

    /// Whether to package these target-specific docs for another similar target.
    pub(crate) fn use_docs_fallback(&self) -> bool {
        matches!(self, PkgType::JsonDocs | PkgType::HtmlDocs | PkgType::RustcDocs)
    }
}

#[derive(Debug, Default, Clone)]
pub(crate) struct VersionInfo {
    pub(crate) version: Option<String>,
    pub(crate) git_commit: Option<String>,
    pub(crate) present: bool,
}

pub(crate) struct Versions {
    channel: String,
    dist_path: PathBuf,
    versions: HashMap<PkgType, VersionInfo>,
}

impl Versions {
    pub(crate) fn new(channel: &str, dist_path: &Path) -> Result<Self, Error> {
        Ok(Self { channel: channel.into(), dist_path: dist_path.into(), versions: HashMap::new() })
    }

    pub(crate) fn channel(&self) -> &str {
        &self.channel
    }

    pub(crate) fn version(&mut self, mut package: &PkgType) -> Result<VersionInfo, Error> {
        if package.should_use_rust_version() {
            package = &PkgType::Rust;
        }

        match self.versions.get(package) {
            Some(version) => Ok(version.clone()),
            None => {
                let mut version_info = self.load_version_from_tarball(package)?;
                if *package == PkgType::Rust && version_info.version.is_none() {
                    // Trust: the umbrella `trust` component (PkgType::Rust) is a
                    // meta-installer that bundles the others; a stage0-seed
                    // snapshot does not need it and may not build it (it pulls
                    // the whole tool set, incl. the linter). Every
                    // `should_use_rust_version()` component shares the toolchain
                    // version, so fall back to the concrete compiler's
                    // (`trustc`) version/git-commit files rather than panicking
                    // with "missing version info for toolchain". This lets the
                    // channel manifest — and therefore `prepare.py` stage0 seed
                    // minting — be produced from just the bootstrap-critical
                    // component tarballs. See docs/OFF_STOCK_RUST_PLAN.md.
                    let rustc_info = self.load_version_from_tarball(&PkgType::Rustc)?;
                    if rustc_info.version.is_some() {
                        version_info = rustc_info;
                    } else {
                        panic!(
                            "missing version info for toolchain: neither the `trust` umbrella \
                             nor the `trustc` component tarball carries a version file in {}",
                            self.dist_path.display()
                        );
                    }
                }
                self.versions.insert(package.clone(), version_info.clone());
                Ok(version_info)
            }
        }
    }

    fn load_version_from_tarball(&mut self, package: &PkgType) -> Result<VersionInfo, Error> {
        for ext in ["xz", "gz"] {
            let info =
                self.load_version_from_tarball_inner(&self.dist_path.join(self.archive_name(
                    package,
                    DEFAULT_TARGET,
                    &format!("tar.{}", ext),
                )?))?;
            if info.present {
                return Ok(info);
            }
        }

        if let Some(tarball) = self.fallback_archive(package)? {
            let info = self.load_version_from_tarball_inner(&tarball)?;
            if info.present {
                return Ok(info);
            }
        }

        // If neither tarball is present, we fallback to returning the non-present info.
        Ok(VersionInfo::default())
    }

    fn fallback_archive(&self, package: &PkgType) -> Result<Option<PathBuf>, Error> {
        let entries = match fs::read_dir(&self.dist_path) {
            Ok(entries) => entries,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(err) => return Err(err.into()),
        };

        let component_name = package.tarball_component_name();
        let version = self.archive_version();
        let prefix = if package.target_independent() {
            format!("{component_name}-{version}.tar.")
        } else {
            format!("{component_name}-{version}-")
        };

        let mut xz_candidates = Vec::new();
        let mut gz_candidates = Vec::new();
        for entry in entries {
            let path = entry?.path();
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if !file_name.starts_with(&prefix) {
                continue;
            }
            if file_name.ends_with(".tar.xz") {
                xz_candidates.push(path);
            } else if file_name.ends_with(".tar.gz") {
                gz_candidates.push(path);
            }
        }

        xz_candidates.sort();
        gz_candidates.sort();
        Ok(xz_candidates.into_iter().next().or_else(|| gz_candidates.into_iter().next()))
    }

    fn load_version_from_tarball_inner(&mut self, tarball: &Path) -> Result<VersionInfo, Error> {
        let file = match File::open(&tarball) {
            Ok(file) => file,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                // Missing tarballs do not return an error, but return empty data.
                println!("warning: missing tarball {}", tarball.display());
                return Ok(VersionInfo::default());
            }
            Err(err) => return Err(err.into()),
        };
        let mut tar: Archive<Box<dyn std::io::Read>> =
            Archive::new(if tarball.extension().map_or(false, |e| e == "gz") {
                Box::new(GzDecoder::new(file))
            } else if tarball.extension().map_or(false, |e| e == "xz") {
                Box::new(XzDecoder::new(file))
            } else {
                unimplemented!("tarball extension not recognized: {}", tarball.display())
            });

        let mut version = None;
        let mut git_commit = None;
        for entry in tar.entries()? {
            let mut entry = entry?;

            let dest;
            match entry.path()?.components().nth(1).and_then(|c| c.as_os_str().to_str()) {
                Some("version") => dest = &mut version,
                Some("git-commit-hash") => dest = &mut git_commit,
                _ => continue,
            }
            let mut buf = String::new();
            entry.read_to_string(&mut buf)?;
            *dest = Some(buf);

            // Short circuit to avoid reading the whole tar file if not necessary.
            if version.is_some() && git_commit.is_some() {
                break;
            }
        }

        Ok(VersionInfo { version, git_commit, present: true })
    }

    pub(crate) fn archive_name(
        &self,
        package: &PkgType,
        target: &str,
        extension: &str,
    ) -> Result<String, Error> {
        let component_name = package.tarball_component_name();
        let version = self.archive_version();

        if package.target_independent() {
            Ok(format!("{}-{}.{}", component_name, version, extension))
        } else {
            Ok(format!("{}-{}-{}.{}", component_name, version, target, extension))
        }
    }

    pub(crate) fn tarball_name(&self, package: &PkgType, target: &str) -> Result<String, Error> {
        self.archive_name(package, target, "tar.gz")
    }

    /// Trust: the product version that names dist archives — Trust's own
    /// `major.minor.dev` line, not the Rust release the toolchain is compatible
    /// with. A `trust-0.1.0` tarball is named after Trust.
    pub(crate) fn trust_version(&self) -> &str {
        const TRUST_VERSION: &str = include_str!("../../../version");
        TRUST_VERSION.trim()
    }

    fn archive_version(&self) -> String {
        match self.channel.as_str() {
            "stable" => self.trust_version().into(),
            "beta" => "beta".into(),
            "nightly" => "nightly".into(),
            "trust" => format!("{}-trust", self.trust_version()),
            _ => format!("{}-dev", self.trust_version()),
        }
    }
}

#[cfg(test)]
mod tests;

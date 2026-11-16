//! Trust: configuration consumes the same original Full owner. Paths remain
//! selection data; only the actual advanced native/Rust owners authorize work.
use super::*;

/// Native-issued runtime selection data, retained beside its actual Full
/// owner. This is neither a held executable nor a Bootstrap shim issuer.
pub(crate) struct Stage0Selection {
    pub(crate) compiler: std::path::PathBuf,
    pub(crate) rustdoc: std::path::PathBuf,
    pub(crate) targo: std::path::PathBuf,
    pub(crate) root: std::path::PathBuf,
    pub(crate) target_libdir: std::path::PathBuf,
    pub(crate) compiler_verbose: String,
}

/// No data constructor: configuration is parsed while the same original
/// source/output/protected scope and native Full continuation stay owned.
pub(crate) struct OriginalBootstrapConfiguration {
    config: Config,
    owner: Arc<OriginalBootstrapCompilation>,
    stage0: Stage0Selection,
}
impl OriginalBootstrapConfiguration {
    pub(crate) fn into_parts(self) -> (Config, Arc<OriginalBootstrapCompilation>, Stage0Selection) {
        (self.config, self.owner, self.stage0)
    }
}

impl OriginalBootstrapCompilation {
    pub(crate) fn configure(self: &Arc<Self>) -> io::Result<OriginalBootstrapConfiguration> {
        self.check_current()?;
        let (arguments, layout) = self.selection();
        let original_source = self.original_source()?.path();
        // A selected source alias must still name the original BEFORE any
        // Config TOML/include reads; the Manager protects its actual root.
        same_source(layout.source(), original_source)?;
        let flags = crate::engine::xpy_flags(arguments)
            .map_err(io::Error::other)?
            .ok_or_else(|| io::Error::other("Full configuration cannot become display-only"))?;
        crate::engine::validate_flags(&flags).map_err(io::Error::other)?;
        if flags.dry_run
            || crate::engine::PreparationScope::for_flags(&flags)
                != crate::engine::PreparationScope::FullEnvelope
        {
            return Err(io::Error::other("original Full request changed its parsed scope"));
        }
        let ceiling = self.cpu_ceiling()?;
        let mut config = self.scoped_work(|| {
            same_source(layout.source(), original_source)?;
            Ok(Config::parse_with_env_and_fixed_budget(
                flags,
                |name| std::env::var_os(name),
                Some(ceiling.get()),
            ))
        })?;
        crate::engine::limit_config(&mut config, ceiling);
        same_source(layout.source(), original_source)?;
        validate_selection(&config, layout)?;
        let seed = &self.data().seed;
        let root = std::path::PathBuf::from(std::ffi::OsStr::from_bytes(&seed.root));
        let stage0 = Stage0Selection {
            compiler: std::path::PathBuf::from(std::ffi::OsStr::from_bytes(&seed.compiler.path)),
            rustdoc: root.join("bin/trustdoc"),
            targo: std::path::PathBuf::from(std::ffi::OsStr::from_bytes(&seed.targo.path)),
            target_libdir: root.join("lib/rustlib/aarch64-apple-darwin/lib"),
            root,
            compiler_verbose: String::from_utf8(
                seed.compiler_queries
                    .iter()
                    .find(|query| query.request.arguments == [b"-vV".to_vec()])
                    .ok_or_else(|| io::Error::other("actual private compiler probe is absent"))?
                    .stdout
                    .clone(),
            )
            .map_err(io::Error::other)?,
        };
        if config.host_target.to_string() != "aarch64-apple-darwin"
            || config.external_rustc.as_ref().is_some_and(|selected| selected != &stage0.compiler)
            || config.external_cargo.as_ref().is_some_and(|selected| selected != &stage0.targo)
            || config.external_rustdoc.as_ref().is_some_and(|selected| selected != &stage0.rustdoc)
        {
            return Err(io::Error::other(
                "Full configuration overrides its actual qualified private seed",
            ));
        }
        self.check_current()?;
        Ok(OriginalBootstrapConfiguration { config, owner: Arc::clone(self), stage0 })
    }
}

fn same_source(selected: &std::path::Path, original: &std::path::Path) -> io::Result<()> {
    if selected.canonicalize()? != original {
        return Err(io::Error::other("Full configuration source alias changed"));
    }
    Ok(())
}

// This is only an additional negative DATA restriction. It cannot manufacture
// a Full owner, source guard, output lock, preparation or resource authority.
fn validate_selection(config: &Config, layout: &InputLayout) -> io::Result<()> {
    if config.src != layout.source()
        || config.out != layout.output()
        || config.dry_run()
        || config.bypass_bootstrap_lock
        || crate::engine::PreparationScope::for_config(config)
            != crate::engine::PreparationScope::FullEnvelope
    {
        return Err(io::Error::other(
            "Full configuration differs from its original source/output request",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests;

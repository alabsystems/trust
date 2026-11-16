//! DATA-only observations at the actual configuration loader seams. No parser,
//! filename inventory, source/cache/home issuer or native completion lives here.
//! Native callers separately retain and enforce their concrete original owners.
use super::*;

#[cfg(unix)]
pub(super) struct Binding {
    observer: Arc<dyn trust_resource_provenance::program::ConfigurationInputObserver>,
    home: PathBuf,
}
#[cfg(unix)]
impl fmt::Debug for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConfigurationInputObservation")
            .finish_non_exhaustive()
    }
}
#[cfg(unix)]
impl Binding {
    fn check(&self, context: &GlobalContext) -> CargoResult<()> {
        self.observer.check_current()?;
        let source = self.observer.root()?;
        anyhow::ensure!(
            context.cwd.starts_with(source)
                && context.home_path.as_path_unlocked() == self.home,
            "configuration changed its bound root or caller-home selection"
        );
        anyhow::ensure!(context.search_stop_path.is_none()
                && context.cli_config.as_ref().is_none_or(|config| config.is_empty()),
            "closed preparation cannot add unbound config overrides or omit ancestors");
        let selected = cargo_util::EnvironmentInputs::from_variables(
            self.observer.environment()?.iter().map(|(key, value)| {
                use std::os::unix::ffi::OsStringExt as _;
                (OsString::from_vec(key.clone()), OsString::from_vec(value.clone()))
            }),
        )?;
        anyhow::ensure!(
            context.env.matches_selected(&selected),
            "configuration changed its original complete environment"
        );
        self.observer.check_current()?;
        Ok(())
    }
    fn record<T>(&self, context: &GlobalContext, result: CargoResult<T>) -> CargoResult<T> {
        match result {
            Ok(value) => match self.check(context) {
                Ok(()) => Ok(value),
                Err(error) => { self.observer.record_failure(); Err(error) }
            },
            Err(error) => { self.observer.record_failure(); Err(error) }
        }
    }
}

impl GlobalContext {
    /// Attach an untrusted observer BEFORE lazy configuration/credential reads.
    /// This retains DATA production through discovery, parse, cached reads and
    /// reloads; it creates no source/cache/native owner or config producer/seal.
    /// Native callers must separately retain their real opaque original owners.
    /// Only that concrete observer may judge unsupported custody roots/links.
    #[cfg(unix)]
    pub fn observe_configuration_inputs(
        &mut self,
        observer: Arc<dyn trust_resource_provenance::program::ConfigurationInputObserver>,
    ) -> CargoResult<()> {
        if self.preparation_configuration.is_some() {
            observer.record_failure();
            if let Some(binding) = &self.preparation_configuration { binding.observer.record_failure(); }
            bail!("original preparation configuration is one-use");
        }
        // Retain the actual issuer BEFORE any fallible validation/read.
        self.preparation_configuration = Some(Binding {
            observer,
            home: self.home_path.clone().into_path_unlocked(),
        });
        let binding = self.preparation_configuration.as_ref().unwrap();
        let result = (|| {
            anyhow::ensure!(!self.values.filled() && !self.credential_values.filled(),
                "original preparation must precede configuration and credential reads");
            binding.check(self)?;
            // Physical membership only. The actual frozen recipe/native owner
            // separately authorizes each source-derived member cwd.
            anyhow::ensure!(matches!(binding.observer.capture_input(&self.cwd)?,
                    trust_resource_provenance::program::SourceRead::Directory),
                "initial configuration cwd is not an observed member directory");
            // Reuse the maintained home selection, with the same immutable
            // frontend-aware environment and its real OS-home fallback.
            let os_home = || self.env.get_env_os("HOME").map(PathBuf::from)
                .or_else(::home::home_dir);
            anyhow::ensure!(homedir_with_environment(&self.cwd, &self.env, os_home)
                    .as_deref() == Some(binding.home.as_path()),
                "configuration caller home differs from its original environment");
            anyhow::ensure!(matches!(binding.observer.capture_input(&binding.home)?,
                    trust_resource_provenance::program::SourceRead::Directory),
                "configuration caller home is not an observed directory");
            Ok(())
        })();
        binding.record(self, result)
    }

    pub(super) fn configuration_override_allowed(&self) -> CargoResult<()> {
        #[cfg(unix)]
        if let Some(binding) = &self.preparation_configuration {
            binding.observer.record_failure();
            bail!("original preparation cannot import caller-authored config rows");
        }
        Ok(())
    }
    pub(super) fn configuration_current(&self) -> CargoResult<()> {
        #[cfg(unix)]
        if let Some(binding) = &self.preparation_configuration {
            return binding.record(self, binding.check(self));
        }
        Ok(())
    }
    pub(super) fn configuration_result<T>(&self, result: CargoResult<T>) -> CargoResult<T> {
        #[cfg(unix)]
        if let Some(binding) = &self.preparation_configuration {
            return binding.record(self, result);
        }
        result
    }
    pub(super) fn configuration_probe(&self, path: &Path) -> CargoResult<()> {
        self.configuration_current()?;
        #[cfg(unix)]
        if let Some(binding) = &self.preparation_configuration {
            let result = binding.observer.capture_input(path).map(|_| ()).map_err(Into::into);
            return binding.record(self, result);
        }
        let _ = path;
        Ok(())
    }
    pub(super) fn configuration_read_to_string(&self, path: &Path) -> CargoResult<String> {
        self.configuration_current()?;
        #[cfg(unix)]
        if let Some(binding) = &self.preparation_configuration {
            let result = (|| match binding.observer.capture_input(path)? {
                trust_resource_provenance::program::SourceRead::File { bytes, .. } => Ok(String::from_utf8(bytes)?),
                _ => bail!("configuration input is not an original readonly regular file"),
            })();
            return binding.record(self, result);
        }
        Ok(fs::read_to_string(path)?)
    }
}

// These execute the ordinary parser at the changed seams. They do not construct
// an admitted native Graph/Root/Seed or claim the unavailable external-root path.
#[cfg(test)]
mod tests {
    use super::*;
    fn context() -> (tempfile::TempDir, GlobalContext) {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().canonicalize().unwrap();
        fs::create_dir(path.join(".cargo")).unwrap();
        let home = path.join("home"); fs::create_dir(&home).unwrap();
        let mut context = GlobalContext::new(Shell::new(), path.clone(), home);
        context.env = Env::from_map(Default::default());
        context.set_search_stop_path(path);
        (root, context)
    }
    #[test]
    fn ordinary_loader_keeps_legacy_preference_recursive_and_optional_includes() {
        let (root, context) = context(); let cargo = root.path().join(".cargo");
        fs::write(cargo.join("config"), "include=['first.toml', { path='optional.toml', optional=true }]\n[net]\noffline=true\n").unwrap();
        fs::write(cargo.join("first.toml"), "include=['nested.toml']\n").unwrap();
        fs::write(cargo.join("nested.toml"), "[http]\ntimeout=31\n").unwrap();
        fs::write(cargo.join("config.toml"), "[net]\noffline=false\n").unwrap();
        assert!(context.get::<bool>(["net", "offline"]).unwrap());
        assert_eq!(context.get::<u32>(["http", "timeout"]).unwrap(),31);
    }
    #[test]
    fn ordinary_loader_keeps_cached_values_until_explicit_reload_and_optional_discovery() {
        let (root, mut context) = context(); let cargo=root.path().join(".cargo");
        fs::write(cargo.join("config.toml"), "include=[{ path='optional.toml', optional=true }]\n[net]\noffline=true\n").unwrap();
        assert!(context.get::<bool>(["net", "offline"]).unwrap());
        fs::write(cargo.join("config.toml"), "include=[{ path='optional.toml', optional=true }]\n[net]\noffline=false\n").unwrap();
        fs::write(cargo.join("optional.toml"), "[http]\ntimeout=83\n").unwrap();
        assert!(context.get::<bool>(["net", "offline"]).unwrap());
        let cwd = context.cwd().to_owned();
        context.reload_rooted_at(cwd).unwrap();
        assert!(!context.get::<bool>(["net", "offline"]).unwrap());
        assert_eq!(context.get::<u32>(["http", "timeout"]).unwrap(),83);
    }
    #[test]
    fn ordinary_configure_keeps_its_documented_tolerant_term_error_behavior() {
        let (root, mut context) = context();
        fs::write(root.path().join(".cargo/config.toml"), "[term]\nverbose='not-a-boolean'\n").unwrap();
        context.configure(0, false, None, false, true, true, &None, &[], &[]).unwrap();
    }
    #[test]
    fn ordinary_loader_keeps_cli_file_selection_and_its_existing_parser_errors() {
        let (root, mut context)=context();
        fs::write(root.path().join("selected.toml"), "[net]\noffline=true\n").unwrap();
        context.cli_config=Some(vec!["selected.toml".to_string()]);
        let parsed=context.cli_args_as_table().unwrap();
        assert!(parsed.is_table());
        fs::write(root.path().join("selected.toml"), "[invalid\n").unwrap();
        let error=context.cli_args_as_table().unwrap_err();
        assert!(format!("{error:#}").contains("could not parse TOML configuration"));
    }
}

// Arbitrary observer success is DATA only. This fixture deliberately has no
// Manager, native Graph, materialization, process/closure, Seed or SDK owner.
// It exercises real parser/hook/cache behavior, not native custody authority.
#[cfg(all(test, unix))]
mod observer_tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering};
    use trust_resource_provenance::program::{ConfigurationInputObserver, SourceRead};
    struct DataObserver {
        root: PathBuf,
        env: Vec<(Vec<u8>, Vec<u8>)>,
        calls: Mutex<Vec<PathBuf>>,
        refused: AtomicBool,
    }
    impl fmt::Debug for DataObserver {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("UntrustedConfigurationDataFixture").finish_non_exhaustive()
        }
    }
    impl ConfigurationInputObserver for DataObserver {
        fn check_current(&self) -> std::io::Result<()> {
            if self.refused.load(Ordering::Acquire) {
                Err(std::io::Error::other("untrusted DATA observer refused"))
            } else { Ok(()) }
        }
        fn root(&self) -> std::io::Result<&Path> { Ok(&self.root) }
        fn environment(&self) -> std::io::Result<&[(Vec<u8>, Vec<u8>)]> { Ok(&self.env) }
        fn capture_input(&self, path: &Path) -> std::io::Result<SourceRead> {
            self.check_current()?;
            self.calls.lock().unwrap().push(path.to_owned());
            // Test DATA only. An actual native source wrapper must refuse these
            // unsupported roots; this fixture grants no completeness/custody.
            if !path.starts_with(&self.root) { return Ok(SourceRead::Absent); }
            match fs::symlink_metadata(path) {
                Ok(m) if m.is_file() => Ok(SourceRead::File { mode:0o100644, bytes:fs::read(path)? }),
                Ok(m) if m.is_dir() => Ok(SourceRead::Directory),
                Err(e) if e.kind()==std::io::ErrorKind::NotFound => Ok(SourceRead::Absent),
                Err(e) => Err(e),
                _ => Err(std::io::Error::other("fixture input is not regular DATA")),
            }
        }
        fn record_failure(&self) { self.refused.store(true, Ordering::Release); }
    }
    fn observed() -> (tempfile::TempDir, GlobalContext, Arc<DataObserver>) {
        let root=tempfile::tempdir().unwrap(); let path=root.path().canonicalize().unwrap();
        fs::create_dir(path.join(".cargo")).unwrap();
        let home=path.join("home");fs::create_dir(&home).unwrap();
        let env=vec![(b"CARGO_HOME".to_vec(), home.as_os_str().as_encoded_bytes().to_vec())];
        let observer=Arc::new(DataObserver { root:path.clone(),env,calls:Mutex::new(Vec::new()),refused:AtomicBool::new(false) });
        let mut context=GlobalContext::new(Shell::new(),path,home);
        let selected=cargo_util::EnvironmentInputs::from_variables(observer.env.iter().map(|(k,v)| {
            use std::os::unix::ffi::OsStringExt as _;
            (OsString::from_vec(k.clone()),OsString::from_vec(v.clone()))
        })).unwrap();
        context.env=Env::from_selected(&selected);
        context.observe_configuration_inputs(observer.clone()).unwrap();
        (root,context,observer)
    }
    #[test]
    fn observer_sees_real_payload_negative_include_candidates_and_member_reload() {
        let (root,mut context,observer)=observed();let cargo=context.cwd().join(".cargo");
        fs::write(cargo.join("config.toml"),"include=['nested.toml',{path='optional.toml',optional=true}]\n[net]\noffline=true\n").unwrap();
        fs::write(cargo.join("nested.toml"),"[http]\ntimeout=31\n").unwrap();
        assert!(context.get::<bool>(["net","offline"]).unwrap());
        assert_eq!(context.http_config().unwrap().timeout,Some(31));
        let member=root.path().join("member");fs::create_dir(&member).unwrap();
        context.reload_directory(member.clone()).unwrap();
        assert!(context.get::<bool>(["net","offline"]).unwrap());
        let calls=observer.calls.lock().unwrap();
        for path in [cargo.join("config"),cargo.join("config.toml"),cargo.join("nested.toml"),cargo.join("optional.toml"),member.join(".cargo/config")] {
            assert!(calls.contains(&path),"ordinary loader did not observe {}",path.display());
        }
        assert!(calls.iter().any(|path| path.as_path() == context.home().as_path_unlocked()));
    }
    #[test]
    fn observer_refusal_rechecks_filled_value_credential_and_typed_caches() {
        let (root,context,observer)=observed();
        fs::write(root.path().join(".cargo/config.toml"),"[net]\noffline=true\n[http]\ntimeout=31\n").unwrap();
        fs::write(context.home().join("credentials.toml").into_path_unlocked(),"[registry]\ntoken='fixture-only'\n").unwrap();
        context.load_credentials().unwrap();context.net_config().unwrap();context.http_config().unwrap();
        observer.refused.store(true,Ordering::Release);
        assert!(context.get::<Option<String>>(["registry","token"]).is_err());
        assert!(context.net_config().is_err());assert!(context.http_config().is_err());
        assert!(context.values().is_err());
    }
    #[test]
    fn scoped_configure_cannot_swallow_a_typed_configuration_refusal() {
        let (root,mut context,observer)=observed();
        fs::write(root.path().join(".cargo/config.toml"),"[term]\nverbose='not-a-boolean'\n").unwrap();
        assert!(context.configure(0,false,None,false,true,true,&None,&[],&[]).is_err());
        assert!(observer.refused.load(Ordering::Acquire));
    }
    #[test]
    fn observer_rows_cannot_replace_the_existing_parser_or_omit_ancestors() {
        let (_root,context,observer)=observed();
        assert!(context.set_values(HashMap::default()).is_err());
        assert!(observer.refused.load(Ordering::Acquire));
        let (root,mut context,observer)=observed();context.set_search_stop_path(root.path());
        assert!(context.load_values().is_err());
        assert!(observer.refused.load(Ordering::Acquire));
    }
}

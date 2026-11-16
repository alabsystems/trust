//! Trust: the original Root's exact full Cargo-library input loop.
//! Only the actual resident owner supplies recipes and checked seed queries.
use super::*;
use crate::util::cache_lock::CacheLockMode;
use anyhow::ensure;
use cargo_util::{
    EnvironmentInputs, ExecStats, Jobserver, ProcessBuilder, ProcessExecutor, StreamingOutputLimits,
};
use std::ffi::OsStr;
use std::ffi::OsString;
use std::io;
use std::os::fd::AsFd as _;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::ffi::OsStringExt as _;
use std::os::unix::process::ExitStatusExt as _;
use std::process::{ExitStatus, Output};
use std::sync::{Arc, Mutex, OnceLock, Weak};
use trust_build_tree::trust_repo_lock::management::OriginalSourceRoot;
use trust_resource_controller::CommandSpec;
use trust_resource_controller::bootstrap_graph::GnuIdentity;
use trust_resource_controller::bootstrap_graph::preparation::Mode;
use trust_resource_controller::bootstrap_graph::preparation::work::QueryStdin;
use trust_resource_controller::client::bootstrap_graph::ResidentDependencyInputs;

/// No public/data constructor. This can only consume the session after every
/// exact real fetch succeeded, including the full final locked/offline pass.
#[must_use]
pub struct FinishedDependencyInputs {
    work: ResidentDependencyInputs,
    queries: Arc<Queries>,
}
impl FinishedDependencyInputs {
    pub fn into_work(self) -> ResidentDependencyInputs {
        self.work
    }

    /// The native operation consumes the SAME completed work and original
    /// source/output owner. No status or saved query can supply that transition.
    pub fn advance(
        self,
        inputs: bootstrap::engine::OriginalDependencyInputs,
    ) -> CargoResult<Arc<super::bootstrap_full::BootstrapFull>> {
        let cargo_home = path(&self.work.data().cargo_home);
        let owner = Arc::new(inputs.advance(self.work)?);
        let full = Arc::new_cyclic(|original_self| super::bootstrap_full::BootstrapFull {
            original_self: original_self.clone(),
            owner,
            scheduler: self.queries.scheduler.clone(),
            implicit_borrowed: std::sync::atomic::AtomicBool::new(false),
            cargo_home,
            environment: self.queries.environment.clone(),
            sequence: std::sync::atomic::AtomicU64::new(1),
            delivery: Mutex::new(()),
        });
        // This private slot can be installed only by this actual consuming
        // transition. Failure cannot restore input queries or raw execution.
        self.queries
            .compilation
            .set(Arc::downgrade(&full))
            .map_err(|_| super::bootstrap_full::AdvanceFailure {
                _owner: Arc::clone(&full),
            })?;
        Ok(full)
    }
}

struct Queries {
    work: Mutex<Option<ResidentDependencyInputs>>,
    scheduler: Jobserver,
    compilation: OnceLock<Weak<super::bootstrap_full::BootstrapFull>>,
    environment: EnvironmentInputs,
}
pub(super) fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
fn retained_deadline(bound: std::time::Instant) -> io::Result<std::time::Instant> {
    if std::time::Instant::now() >= bound {
        return Err(io::ErrorKind::TimedOut.into());
    }
    Ok(bound)
}
fn deadline(work: &ResidentDependencyInputs) -> io::Result<std::time::Instant> {
    let now = std::time::Instant::now();
    let bound = now
        .checked_add(std::time::Duration::from_secs(8))
        .ok_or_else(|| io::Error::other("input check deadline overflow"))?
        .min(work.original_deadline());
    retained_deadline(bound)
}
pub(super) fn issued_environment(command: &CommandSpec) -> io::Result<EnvironmentInputs> {
    EnvironmentInputs::from_variables(command.environment.iter().map(|(key, value)| {
        (
            OsString::from_vec(key.clone()),
            OsString::from_vec(value.clone()),
        )
    }))
    .map_err(io::Error::other)
}
pub(super) fn same_scheduler(scheduler: &Jobserver, gnu: &GnuIdentity) -> io::Result<()> {
    let (read, write) = match scheduler.client().transport_witnesses()? {
        jobserver::TransportWitnesses::NumericPipe { read, write } => (read, write),
        jobserver::TransportWitnesses::NamedFifo { read, write, .. } => (read, write),
    };
    trust_resource_controller::bootstrap_graph::transport::check_gnu_identity(
        gnu,
        &[read.as_fd(), write.as_fd()],
    )
}
fn matches_projection(
    issued: &CommandSpec,
    stdin: QueryStdin,
    gnu: &GnuIdentity,
    command: &ProcessBuilder,
    scheduler: &Jobserver,
) -> io::Result<bool> {
    same_scheduler(scheduler, gnu)?;
    let Some(actual) = command.get_jobserver() else {
        return Ok(false);
    };
    if same_scheduler(actual, gnu).is_err() {
        return Ok(false);
    }
    if command.get_program().as_encoded_bytes() != issued.program
        || command.get_arg0().map(OsStr::as_encoded_bytes) != issued.arg0.as_deref()
        || command.get_cwd().map(|p| p.as_os_str().as_bytes()) != Some(issued.cwd.as_slice())
        || !command
            .get_args()
            .map(|arg| arg.as_encoded_bytes())
            .eq(issued.args.iter().map(Vec::as_slice))
        || !matches!(stdin, QueryStdin::Null)
        || command.get_stdin().is_some()
        || !command.has_jobserver()
    {
        return Ok(false);
    }
    // Rebind ONLY descriptor spelling from the SAME actual GNU scheduler.
    // Native-issued runtime/loader/cwd/argv/env bytes remain exact DATA. This
    // metadata builder never executes, imports a resource marker, or gets GO.
    let mut expected = ProcessBuilder::new(path(&issued.program));
    expected
        .environment_snapshot(issued_environment(issued)?)
        .inherit_jobserver(scheduler);
    Ok(command.get_effective_envs()? == expected.get_effective_envs()?)
}
impl ProcessExecutor for Queries {
    fn output(&self, command: &ProcessBuilder) -> io::Result<Output> {
        let work = self
            .work
            .lock()
            .map_err(|_| io::Error::other("resident input query owner poisoned"))?;
        let Some(work) = work.as_ref() else {
            // Do not hold the old input slot over the actual Full owner call.
            drop(work);
            return self
                .compilation
                .get()
                .and_then(Weak::upgrade)
                .ok_or_else(|| io::Error::other("resident compiler-query scope is closed"))?
                .compiler_output(command);
        };
        retained_output(
            &work.data().compiler_queries,
            command,
            &self.scheduler,
            || work.check_current(deadline(work)?),
        )
    }
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        Err(io::Error::other(
            "dependency inputs refuse external status execution",
        ))
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        (
            ExecStats::default(),
            Err(anyhow!(
                "dependency inputs refuse external streaming execution"
            )),
        )
    }
}

// The complete projection matcher and captured bytes are shared unchanged;
// only the actual owning phase supplies its live bookend operation.
pub(super) fn retained_output(
    queries: &[trust_resource_controller::bootstrap_graph::preparation::work::RetainedCompilerQuery],
    command: &ProcessBuilder,
    scheduler: &Jobserver,
    current: impl Fn() -> io::Result<()>,
) -> io::Result<Output> {
    current()?;
    for issued in queries {
        same_scheduler(scheduler, &issued.request.gnu)?;
        issued.request.validate_prepared(&issued.prepared)?;
        if matches_projection(
            &issued.command,
            issued.stdin,
            &issued.request.gnu,
            command,
            scheduler,
        )? {
            current()?;
            return Ok(Output {
                status: ExitStatus::from_raw(0),
                stdout: issued.stdout.clone(),
                stderr: issued.stderr.clone(),
            });
        }
    }
    Err(io::Error::other(
        "resident compiler query differs from every actual native-issued complete projection",
    ))
}

/// Resolve every source-declared recipe with the SAME early scheduler and
/// actual protected source. No recipe subset or synthetic completion callback
/// is accepted. The native owner's SourceCacheGuard stays live throughout;
/// this one Cargo context keeps real package-cache guards through each pass.
pub fn fetch_all(
    work: ResidentDependencyInputs,
    source: &OriginalSourceRoot,
    scheduler: &Jobserver,
    entry: &GlobalContext,
) -> CargoResult<FinishedDependencyInputs> {
    source.check_current()?;
    work.check_current(deadline(&work)?)?;
    let data = work.data().clone();
    data.validate()?;
    ensure!(
        path(&data.source) == source.path(),
        "resident inputs changed the actual source owner"
    );
    ensure!(
        entry.home().as_path_unlocked() == path(&data.cargo_home),
        "resident inputs changed the original admission-owned Cargo home"
    );
    let mut values = EnvironmentInputs::capture()?
        .iter()
        .map(|(key, value)| (key.to_owned(), value.to_owned()))
        .collect::<std::collections::BTreeMap<_, _>>();
    // Selection DATA from the actual held native seed, never an owner import.
    values.insert("RUSTC".into(), path(&data.compiler.path).into_os_string());
    values.insert("CARGO_HOME".into(), path(&data.cargo_home).into_os_string());
    let environment = EnvironmentInputs::from_variables(values)?;
    let queries = Arc::new(Queries {
        work: Mutex::new(Some(work)),
        scheduler: scheduler.clone(),
        compilation: OnceLock::new(),
        environment: environment.clone(),
    });
    // This distinct closed CLI entry terminates after the loop. Keep a permanent
    // refusing executor installed so credential/Git helpers can never fall back
    // to unowned local subprocesses. After completion the slot is empty; it
    // retains no source borrower and can issue no further retained query data.
    cargo_util::install_process_executor(queries.clone())?;
    let mut gctx = GlobalContext::for_coordinator_queries(
        Shell::new(),
        source.path().to_owned(),
        path(&data.cargo_home),
        path(&data.seed_root).join("bin/targo"),
        environment,
        scheduler.clone(),
        queries.clone(),
    )?;
    let issued = data
        .compiler_queries
        .iter()
        .map(|issued| {
            same_scheduler(scheduler, &issued.request.gnu)?;
            Ok((
                OsString::from_vec(issued.command.program.clone()),
                issued
                    .command
                    .args
                    .iter()
                    .cloned()
                    .map(OsString::from_vec)
                    .collect(),
                issued_environment(&issued.command)?,
            ))
        })
        .collect::<io::Result<Vec<_>>>()?;
    gctx.coordinator_queries = gctx
        .coordinator_queries
        .take()
        .map(|scope| scope.with_issued_environments(issued));
    let passes: &[bool] = match data.attempt.mode {
        Mode::Check => &[true],
        Mode::Prepare => &[false, true],
    };
    for &offline in passes {
        gctx.configure(0, false, None, false, true, offline, &None, &[], &[])?;
        ensure!(
            gctx.cli_unstable().build_std.is_none(),
            "resident all-target input envelope cannot select build-std"
        );
        let cache = gctx
            .try_acquire_package_cache_lock(CacheLockMode::Shared)?
            .ok_or_else(|| {
                anyhow!("original Cargo cache is busy; resident input ownership retained")
            })?;
        cache.check_actual_shared()?;
        for manifest in &data.manifests {
            source.check_current()?;
            cache.check_actual_shared()?;
            {
                let work = queries
                    .work
                    .lock()
                    .map_err(|_| anyhow!("resident inputs poisoned"))?;
                let work = work
                    .as_ref()
                    .ok_or_else(|| anyhow!("resident input work is closed"))?;
                work.check_current(deadline(work)?)?;
            }
            let manifest = source.path().join(path(manifest));
            let ws = crate::workspace::Workspace::new(&manifest, &gctx)?;
            let result = crate::ops::fetch(
                &ws,
                &crate::ops::FetchOptions {
                    gctx: &gctx,
                    targets: Vec::new(),
                },
            )?;
            drop(result);
            drop(ws);
            source.check_current()?;
            cache.check_actual_shared()?;
            let mut work = queries
                .work
                .lock()
                .map_err(|_| anyhow!("resident inputs poisoned"))?;
            let work = work
                .as_mut()
                .ok_or_else(|| anyhow!("resident input work is closed"))?;
            work.check_current(deadline(work)?)?;
            // SAFETY: only after this exact real ops::fetch returned success,
            // with locked + native planned offline mode, SAME source/context,
            // original scheduler, and both actual source/native postchecks.
            // A checkpoint owns the real managed source-planner replay. The
            // short read-only observation budget cannot bound that work. Keep
            // the SAME original phase endpoint; never reset or extend it.
            let at = retained_deadline(work.original_deadline())?;
            unsafe {
                work.recipe_completed(at)?;
            }
        }
    }
    source.check_current()?;
    drop(gctx);
    let work = queries
        .work
        .lock()
        .map_err(|_| anyhow!("resident input work poisoned"))?
        .take()
        .ok_or_else(|| anyhow!("resident input work already consumed"))?;
    work.check_current(deadline(&work)?)?;
    Ok(FinishedDependencyInputs { work, queries })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn planner_checkpoint_keeps_the_original_phase_bound_without_revival() {
        use std::time::{Duration, Instant};
        let original = Instant::now() + Duration::from_secs(60);
        let observation = Instant::now() + Duration::from_secs(8);
        let checkpoint = retained_deadline(original).unwrap();
        assert_eq!(checkpoint, original);
        assert!(checkpoint > observation);
        assert_eq!(retained_deadline(original).unwrap(), checkpoint);
        assert!(retained_deadline(Instant::now() - Duration::from_secs(1)).is_err());
    }
    #[test]
    fn real_all_target_fetch_keeps_conditional_dependencies_without_target_probes() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        struct Refuse(AtomicUsize);
        impl ProcessExecutor for Refuse {
            fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
                self.0.fetch_add(1, Ordering::SeqCst);
                Err(io::Error::other("fixture refuses every compiler query"))
            }
            fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
                panic!("fetch cannot execute status")
            }
            fn streaming(
                &self,
                _: &ProcessBuilder,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: bool,
                _: Option<StreamingOutputLimits>,
                _: bool,
            ) -> (ExecStats, CargoResult<Output>) {
                panic!("fetch cannot execute streaming")
            }
        }
        let root = tempfile::tempdir().unwrap();
        let source = root.path().canonicalize().unwrap();
        let home = source.join("home");
        std::fs::create_dir_all(source.join("src")).unwrap();
        std::fs::create_dir_all(source.join("dep/src")).unwrap();
        std::fs::create_dir(&home).unwrap();
        std::fs::write(source.join("Cargo.toml"),"[package]\nname='resident-fetch-fixture'\nversion='0.1.0'\nedition='2021'\n[target.'cfg(target_os=\"imaginary\")'.dependencies]\nconditional-dep={path='dep'}\n").unwrap();
        std::fs::write(source.join("src/lib.rs"), "").unwrap();
        std::fs::write(
            source.join("dep/Cargo.toml"),
            "[package]\nname='conditional-dep'\nversion='0.1.0'\nedition='2021'\n",
        )
        .unwrap();
        std::fs::write(source.join("dep/src/lib.rs"), "").unwrap();
        let lock=b"version = 4\n\n[[package]]\nname = \"conditional-dep\"\nversion = \"0.1.0\"\n\n[[package]]\nname = \"resident-fetch-fixture\"\nversion = \"0.1.0\"\ndependencies = [\n \"conditional-dep\",\n]\n";
        std::fs::write(source.join("Cargo.lock"), lock).unwrap();
        let executor = Arc::new(Refuse(AtomicUsize::new(0)));
        let environment = EnvironmentInputs::from_variables([(
            OsString::from("RUSTC"),
            source.join("no-compiler").into_os_string(),
        )])
        .unwrap();
        let mut gctx = GlobalContext::for_coordinator_queries(
            Shell::new(),
            source.clone(),
            home,
            std::env::current_exe().unwrap(),
            environment,
            Jobserver::new(0).unwrap(),
            executor.clone(),
        )
        .unwrap();
        gctx.configure(
            0,
            false,
            None,
            false,
            true,
            true,
            &None,
            &[],
            &["resolver.incompatible-rust-versions='allow'".into()],
        )
        .unwrap();
        let ws = crate::workspace::Workspace::new(&source.join("Cargo.toml"), &gctx).unwrap();
        let (resolve, packages) = crate::ops::fetch(
            &ws,
            &crate::ops::FetchOptions {
                gctx: &gctx,
                targets: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(
            resolve.iter().count(),
            2,
            "all-target envelope retains conditional dependency"
        );
        assert_eq!(
            executor.0.load(Ordering::SeqCst),
            0,
            "unused target facts require no query"
        );
        drop(packages);
        drop(resolve);
        assert_eq!(std::fs::read(source.join("Cargo.lock")).unwrap(), lock);
        drop(ws);
        // Real online all-target fetch reaches routine auto-GC. The SAME
        // retained Shared guard must cause a nonblocking refusal, not panic.
        gctx.configure(0, false, None, false, true, false, &None, &[], &[])
            .unwrap();
        let cache = gctx
            .try_acquire_package_cache_lock(CacheLockMode::Shared)
            .unwrap()
            .unwrap();
        cache.check_actual_shared().unwrap();
        assert!(
            gctx.try_acquire_package_cache_lock(CacheLockMode::MutateExclusive)
                .unwrap()
                .is_none()
        );
        let ws = crate::workspace::Workspace::new(&source.join("Cargo.toml"), &gctx).unwrap();
        let fetched = crate::ops::fetch(
            &ws,
            &crate::ops::FetchOptions {
                gctx: &gctx,
                targets: Vec::new(),
            },
        )
        .unwrap();
        drop(fetched);
        assert_eq!(executor.0.load(Ordering::SeqCst), 0);
        drop(cache);
        assert!(
            gctx.try_acquire_package_cache_lock(CacheLockMode::MutateExclusive)
                .unwrap()
                .is_some()
        );
        assert!(
            crate::ops::fetch(
                &ws,
                &crate::ops::FetchOptions {
                    gctx: &gctx,
                    targets: vec!["aarch64-apple-darwin".into()]
                }
            )
            .is_err(),
            "explicit target still needs real compiler capabilities"
        );
    }

    #[test]
    fn full_issued_query_refuses_cwd_env_stdin_arg0_and_argv_mutations() {
        let scheduler = Jobserver::new(0).unwrap();
        use std::os::unix::fs::MetadataExt as _;
        let (read, write) = match scheduler.client().transport_witnesses().unwrap() {
            jobserver::TransportWitnesses::NumericPipe { read, write } => (read, write),
            _ => panic!("fixture owns its actual numeric pipe"),
        };
        let id = |fd| {
            let m = std::fs::File::from(fd).metadata().unwrap();
            trust_resource_controller::FileIdentity {
                device: m.dev(),
                inode: m.ino(),
            }
        };
        let gnu = GnuIdentity::NumericPipe {
            read: id(read),
            write: id(write),
        };
        let issued = CommandSpec {
            program: b"/seed/bin/trustc".to_vec(),
            arg0: None,
            args: vec![b"-vV".to_vec()],
            cwd: b"/source".to_vec(),
            environment: vec![(b"LANG".to_vec(), b"C".to_vec())],
        };
        let build = || {
            let mut p = ProcessBuilder::new(path(&issued.program));
            p.arg("-vV")
                .cwd(path(&issued.cwd))
                .environment_snapshot(issued_environment(&issued).unwrap())
                .inherit_jobserver(&scheduler);
            p
        };
        struct Refuse;
        impl ProcessExecutor for Refuse {
            fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
                panic!("projection configuration cannot execute")
            }
            fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
                panic!("projection configuration cannot execute")
            }
            fn streaming(
                &self,
                _: &ProcessBuilder,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: &mut dyn FnMut(&str) -> CargoResult<()>,
                _: bool,
                _: Option<StreamingOutputLimits>,
                _: bool,
            ) -> (ExecStats, CargoResult<Output>) {
                panic!("projection configuration cannot execute")
            }
        }
        let scope = super::super::compiler_query::Scoped::new(
            issued_environment(&issued).unwrap(),
            scheduler.clone(),
            Arc::new(Refuse),
            path(&issued.cwd),
        )
        .with_issued_environments(vec![(
            OsString::from_vec(issued.program.clone()),
            issued
                .args
                .iter()
                .cloned()
                .map(OsString::from_vec)
                .collect(),
            issued_environment(&issued).unwrap(),
        )]);
        let mut defaults = ProcessBuilder::new(path(&issued.program));
        defaults.arg("-vV");
        scope.configure(&mut defaults);
        assert!(
            matches_projection(&issued, QueryStdin::Null, &gnu, &defaults, &scheduler).unwrap()
        );
        let mut before = build();
        before.environment_snapshot(
            EnvironmentInputs::from_variables([(
                "LANG".into(),
                "foreign-captured-baseline".into(),
            )])
            .unwrap(),
        );
        scope.configure(&mut before);
        assert!(!matches_projection(&issued, QueryStdin::Null, &gnu, &before, &scheduler).unwrap());
        let mut before = build();
        before.cwd("/foreign-before-config");
        scope.configure(&mut before);
        assert!(!matches_projection(&issued, QueryStdin::Null, &gnu, &before, &scheduler).unwrap());
        let foreign = Jobserver::new(0).unwrap();
        let mut before = build();
        before.inherit_jobserver(&foreign);
        scope.configure(&mut before);
        assert!(!matches_projection(&issued, QueryStdin::Null, &gnu, &before, &scheduler).unwrap());
        let mut before = build();
        before.env("LANG", "unissued-before-config");
        scope.configure(&mut before);
        assert!(!matches_projection(&issued, QueryStdin::Null, &gnu, &before, &scheduler).unwrap());
        let original = build();
        assert!(
            matches_projection(&issued, QueryStdin::Null, &gnu, &original, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.cwd("/other");
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.env("LANG", "different");
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.env("EXTRA", "unissued");
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.stdin(Vec::new());
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.arg0("forged");
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let mut changed = build();
        changed.arg("--print=sysroot");
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
        let other = Jobserver::new(0).unwrap();
        let mut changed = build();
        changed.inherit_jobserver(&other);
        assert!(
            !matches_projection(&issued, QueryStdin::Null, &gnu, &changed, &scheduler).unwrap()
        );
    }
}

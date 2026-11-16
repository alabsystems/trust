//! Original compile-directory leases, moved into the nonClone workload capsule.
//! Paths, digests and reports cannot construct these live guards.
use crate::util::{CargoResult, FileLock};
use std::path::Path;

pub(crate) struct OriginalOutputLeases {
    guards: Vec<FileLock>,
    // LAST: actual original paths/guards close before their native FD capacity.
    _retention: Option<std::sync::Arc<dyn Send + Sync>>,
}
impl std::fmt::Debug for OriginalOutputLeases {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalOutputLeases")
            .field("guards", &self.guards)
            .finish_non_exhaustive()
    }
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
struct NativeLeaseRetention {
    _inputs: std::sync::Arc<crate::ops::cargo_test::workload::Inputs>,
    _descriptors: trust_resource_controller::descriptors::OriginalInputPermit,
}

#[derive(Debug)]
pub(crate) struct OutputLeasePopulationRefusal {
    pub(crate) observed: usize,
    pub(crate) maximum: usize,
}
impl std::fmt::Display for OutputLeasePopulationRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "complete original Layout guard population {} exceeds native bound {} before compilation",
            self.observed, self.maximum
        )
    }
}
impl std::error::Error for OutputLeasePopulationRefusal {}
impl OriginalOutputLeases {
    /// Acquire the actual ordinary directory guards before coordinator
    /// admission. This resolves no unit graph and compiles no code. Later
    /// ordinary from_originals must consume the complete SAME lock population.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn prepare_native(
        ws: &crate::workspace::Workspace<'_>,
        config: &crate::compiler::BuildConfig,
        inputs: std::sync::Arc<crate::ops::cargo_test::workload::Inputs>,
        registry: &std::sync::Arc<crate::resource_v3::native_job::outputs::Outputs>,
        preparation: &crate::compiler::native_job::NativeLocalPreparation,
    ) -> CargoResult<std::sync::Arc<Self>> {
        use anyhow::Context as _;
        let startup = crate::resource_v3::native_job::require(registry.plan())?;
        preparation.require(&startup)?;
        let budget = startup
            .descriptor_budget
            .as_ref()
            .context("native Layout preparation lost actual descriptor budget")?;
        // Native Host only: three real Layout locks plus one validation/open
        // scratch descriptor. This charge precedes every new Layout open.
        let descriptors = budget.reserve_original_inputs(4)?;
        inputs.validate_target(&ws.target_dir().into_path_unlocked())?;
        inputs
            .native_selected_root()
            .context("native Layout preparation has no selected original root")?
            .validate(inputs.evidence.deadline())?;
        if let Some(original) = registry.leases(&inputs)? {
            preparation.require(&startup)?;
            return Ok(original);
        }
        let mut layouts = super::layouts::PreparedLayouts::acquire_native(
            ws,
            config,
            inputs.held_output_root().path(),
        )?;
        layouts.prepare()?;
        let guards = layouts.take_compile_leases()?;
        let mut original = Self::from_original_layouts(guards, inputs.held_output_root().path())?;
        inputs.validate()?;
        preparation.require(&startup)?;
        let retention: std::sync::Arc<dyn Send + Sync> =
            std::sync::Arc::new(NativeLeaseRetention {
                _inputs: inputs.clone(),
                _descriptors: descriptors,
            });
        for guard in &mut original.guards {
            guard.retain_original_resources(retention.clone(), budget.clone())?;
        }
        original._retention = Some(retention);
        let original = std::sync::Arc::new(original);
        registry.retain_leases(&inputs, original.clone())?;
        preparation.require(&startup)?;
        Ok(original)
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn from_coordinator_originals(
        originals: &trust_resource_controller::client::CoordinatorOriginals,
        deadline: std::time::Instant,
    ) -> CargoResult<Self> {
        use std::os::unix::ffi::OsStringExt as _;
        originals.validate(deadline)?;
        let request = &originals.observation().outputs;
        request.validate()?;
        anyhow::ensure!(
            originals.outputs().len() == request.locks.len(),
            "coordinator lost complete original Layout population"
        );
        let guards = (0..request.locks.len())
            .map(|index| FileLock::from_coordinator_original(originals, index, deadline))
            .collect::<CargoResult<Vec<_>>>()?;
        let leases = Self {
            guards,
            _retention: None,
        };
        let root =
            std::path::PathBuf::from(std::ffi::OsString::from_vec(request.output_root.clone()));
        leases.validate(&root)?;
        originals.validate(deadline)?;
        Ok(leases)
    }
    #[cfg(all(test, unix))]
    pub(crate) fn actual_layout_fixture(cwd: &Path) -> Self {
        let (guards, _) = tests::actual_layout_guards(cwd);
        Self::from_original_layouts(guards, &cwd.join("target")).unwrap()
    }
    pub(super) fn from_original_layouts(guards: Vec<FileLock>, root: &Path) -> CargoResult<Self> {
        let mut leases = Self {
            guards,
            _retention: None,
        };
        leases.validate(root)?;
        // Change release semantics BEFORE this owner can export any borrowed
        // description. Even ambiguous delivery or Rust unwinding must not
        // unlock the same OFD still retained by the original native host.
        for guard in &mut leases.guards {
            guard.close_only_on_drop();
        }
        Ok(leases)
    }
    /// Export the COMPLETE original census and borrow only its already held
    /// close-only descriptions. No matching pathname can construct this owner,
    /// and a population beyond the fixed transport bound is never truncated.
    #[cfg(unix)]
    pub(crate) fn output_offer(
        &self,
        key: trust_resource_controller::workload::host::output::Key,
        root: &Path,
    ) -> CargoResult<(
        trust_resource_controller::workload::host::output::Request,
        Vec<std::os::fd::BorrowedFd<'_>>,
    )> {
        use std::os::fd::AsFd;
        use std::os::unix::{ffi::OsStrExt, fs::MetadataExt};
        use trust_resource_controller::{FileIdentity, workload::host::output};
        self.validate(root)?;
        if self.guards.len() > output::MAX_LOCKS {
            return Err(OutputLeasePopulationRefusal {
                observed: self.guards.len(),
                maximum: output::MAX_LOCKS,
            }
            .into());
        }
        let mut locks = Vec::with_capacity(self.guards.len());
        let mut originals = Vec::with_capacity(self.guards.len());
        for guard in &self.guards {
            let meta = guard.file().metadata()?;
            locks.push(output::Lock {
                path: guard.path().as_os_str().as_bytes().to_vec(),
                backing: FileIdentity {
                    device: meta.dev(),
                    inode: meta.ino(),
                },
            });
            originals.push(guard.file().as_fd());
        }
        let request = output::Request {
            key,
            output_root: root.as_os_str().as_bytes().to_vec(),
            locks,
        };
        request.validate()?;
        Ok((request, originals))
    }
    pub(crate) fn validate(&self, root: &Path) -> CargoResult<()> {
        anyhow::ensure!(
            !self.guards.is_empty(),
            "native workload has no original output leases"
        );
        for guard in &self.guards {
            anyhow::ensure!(
                guard.path().starts_with(root),
                "workload output lease escapes original output root"
            );
            anyhow::ensure!(
                guard.path().canonicalize()?.as_path() == guard.path(),
                "original workload output lock path is not canonical"
            );
            let held = guard.file().metadata()?;
            let named = std::fs::symlink_metadata(guard.path())?;
            anyhow::ensure!(
                held.is_file() && named.is_file() && !named.file_type().is_symlink(),
                "original workload output lock entry changed kind"
            );
            #[cfg(unix)]
            {
                use std::os::unix::fs::MetadataExt as _;
                anyhow::ensure!(
                    (held.dev(), held.ino()) == (named.dev(), named.ino())
                        && held.nlink() == 1
                        && named.nlink() == 1,
                    "original workload output lock entry was replaced or aliased"
                );
            }
            #[cfg(not(unix))]
            anyhow::bail!("native workload output-lease identity unavailable");
        }
        Ok(())
    }
    /// Same-root sequential Cargo workspaces reuse the actual Layout OFDs;
    /// reopening and flocking their path would deadlock against this owner.
    /// The native queue must independently join/park its current writers before
    /// installing these guards in the next workspace. This is custody only.
    pub(crate) fn borrow_for_workspace(&self, root: &Path) -> CargoResult<Vec<FileLock>> {
        self.validate(root)?;
        let guards = self
            .guards
            .iter()
            .map(FileLock::borrow_close_only)
            .collect::<CargoResult<Vec<_>>>()?;
        self.validate(root)?;
        Ok(guards)
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::compiler::Layout;
    use crate::util::{GlobalContext, flock};
    use crate::workspace::Workspace;
    use cargo_util_terminal::Shell;
    use std::io::Write as _;
    const PROBE: &str = "TARGO_TEST_ORIGINAL_OUTPUT_LEASE_PROBE";
    const BLOCKED: &str = "TARGO_TEST_ORIGINAL_OUTPUT_LEASE_BLOCKED";
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "child lock probe reads its parent's actual environment before a Cargo context exists"
    )]
    fn actual_child_probes_original_output_directory_locks() {
        let Some(paths) = std::env::var_os(PROBE) else {
            return;
        };
        let paths: Vec<std::path::PathBuf> =
            serde_json::from_slice(paths.as_encoded_bytes()).unwrap();
        let blocked = std::env::var_os(BLOCKED).as_deref() == Some(std::ffi::OsStr::new("1"));
        for path in paths {
            let file = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
                .unwrap();
            let result = flock::try_lock_exclusive(&file);
            if blocked {
                assert!(
                    matches!(result, Err(std::fs::TryLockError::WouldBlock)),
                    "original lock did not exclude child writer: {}: {result:?}",
                    path.display()
                );
            } else {
                result.unwrap();
            }
        }
        println!("native-output-lease-probe-ok");
    }
    fn probe(paths: &[std::path::PathBuf], blocked: bool) {
        let mut command = cargo_util::ProcessBuilder::new(std::env::current_exe().unwrap());
        command.args(&["--exact","compiler::build_runner::workload_leases::tests::actual_child_probes_original_output_directory_locks","--nocapture"])
            .env(PROBE,serde_json::to_string(paths).unwrap()).env(BLOCKED,if blocked{"1"}else{"0"});
        let output = command.exec_with_capture(
            cargo_util::StreamingOutputLimits::new(64 * 1024, 1024 * 1024)
                .with_timeout(std::time::Duration::from_secs(60))
                .with_child_exit_cleanup(),
        );
        assert!(
            output.succeeded()
                && output.complete()
                && output.read_error.is_none()
                && output.cleanup_error.is_none(),
            "native lock probe incomplete/failed: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("native-output-lease-probe-ok"),
            "the actual child lock probe did not run"
        );
    }

    #[test]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn native_preparation_capacity_survives_every_real_layout_borrow() {
        // Actual OS locks and descriptor capacity only, no native Root/SDK/
        // CPU/producer or retirement stand-in is constructed by this fixture.
        struct Fee {
            _original: trust_resource_controller::descriptors::OriginalInputPermit,
        }
        let budget =
            trust_resource_controller::descriptors::DescriptorBudget::for_preparation(1, 0)
                .unwrap();
        let owner = std::sync::Arc::new(Fee {
            _original: budget.reserve_original_inputs(4).unwrap(),
        });
        let held = std::sync::Arc::downgrade(&owner);
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        let (guards, paths) = actual_layout_guards(&cwd);
        let mut original =
            OriginalOutputLeases::from_original_layouts(guards, &cwd.join("target")).unwrap();
        for guard in &mut original.guards {
            guard
                .retain_original_resources(owner.clone(), budget.clone())
                .unwrap();
        }
        drop(owner);
        let borrowed = original.borrow_for_workspace(&cwd.join("target")).unwrap();
        drop(original);
        assert!(
            held.upgrade().is_some(),
            "raw borrowed FDs cannot detach their original capacity owner"
        );
        probe(&paths, true);
        let last = borrowed[0].borrow_close_only().unwrap();
        drop(borrowed);
        assert!(held.upgrade().is_some());
        probe(&paths[..1], true);
        drop(last);
        assert!(
            held.upgrade().is_none(),
            "the original capacity closes only after the last actual lock FD"
        );
        probe(&paths, false);
    }

    #[test]
    fn shared_real_layout_preparation_keeps_complete_build_and_check_populations() {
        for (intent, count) in [
            (crate::compiler::UserIntent::Build, 3),
            (crate::compiler::UserIntent::Check { test: false }, 2),
        ] {
            let temporary = tempfile::tempdir().unwrap();
            let cwd = temporary.path().canonicalize().unwrap();
            let (guards, _) = actual_layout_guards(&cwd);
            drop(guards);
            let mut context = GlobalContext::new(
                Shell::from_write(Box::new(Vec::<u8>::new())),
                cwd.clone(),
                cwd.join("cargo-home"),
            );
            context.set_env(Default::default());
            context.set_search_stop_path(&cwd);
            context
                .configure(0, false, None, false, false, true, &None, &[], &[])
                .unwrap();
            let workspace = Workspace::new(&cwd.join("Cargo.toml"), &context).unwrap();
            let config =
                crate::compiler::BuildConfig::new(&context, None, false, &[], intent).unwrap();
            let mut prepared = super::super::layouts::PreparedLayouts::acquire_native(
                &workspace,
                &config,
                &cwd.join("target"),
            )
            .unwrap();
            prepared.prepare().unwrap();
            let guards = prepared.take_compile_leases().unwrap();
            assert_eq!(guards.len(), count);
            assert!(
                prepared.take_compile_leases().is_err(),
                "the same Layout cannot mint a second guard set"
            );
            let paths = guards
                .iter()
                .map(|guard| guard.path().to_owned())
                .collect::<Vec<_>>();
            let original = std::sync::Arc::new(
                OriginalOutputLeases::from_original_layouts(guards, &cwd.join("target")).unwrap(),
            );
            let kinds = [crate::compiler::CompileKind::Host].into_iter().collect();
            let mut next = super::super::layouts::PreparedLayouts::acquire(
                &workspace,
                &kinds,
                "debug",
                matches!(intent, crate::compiler::UserIntent::Build),
                true,
                Some(&original),
            )
            .unwrap();
            drop(original);
            probe(&paths, true);
            let guards = next.take_compile_leases().unwrap();
            assert_eq!(guards.len(), count);
            drop(next);
            probe(&paths, true);
            drop(guards);
            probe(&paths, false);
        }
    }

    #[test]
    fn sequential_workspace_borrows_same_layout_descriptions_until_the_last_owner_closes() {
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        let (guards, paths) = actual_layout_guards(&cwd);
        assert!(
            guards
                .iter()
                .all(|guard| guard.borrow_close_only().is_err()),
            "ordinary Layout guards must not silently change release semantics"
        );
        let capsule =
            OriginalOutputLeases::from_original_layouts(guards, &cwd.join("target")).unwrap();
        let borrowed = capsule.borrow_for_workspace(&cwd.join("target")).unwrap();
        assert_eq!(borrowed.len(), paths.len());
        probe(&paths, true);
        drop(capsule);
        probe(&paths, true);
        drop(borrowed);
        probe(&paths, false);
    }

    #[test]
    fn next_real_layout_uses_original_guards_and_refuses_missing_profiles_without_relocking() {
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        let (guards, paths) = actual_layout_guards(&cwd);
        let capsule =
            OriginalOutputLeases::from_original_layouts(guards, &cwd.join("target")).unwrap();
        let mut context = GlobalContext::new(
            Shell::from_write(Box::new(Vec::<u8>::new())),
            cwd.clone(),
            cwd.join("cargo-home"),
        );
        context.set_env(Default::default());
        context.set_search_stop_path(&cwd);
        context
            .configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&cwd.join("Cargo.toml"), &context).unwrap();
        let mut missing = capsule.borrow_for_workspace(&cwd.join("target")).unwrap();
        assert!(
            Layout::from_originals(&workspace, None, "release", true, true, &mut missing).is_err()
        );
        assert!(
            !cwd.join("target/release/.cargo-build-lock").exists(),
            "a missing original must never reacquire a lock"
        );
        assert_eq!(missing.len(), paths.len());
        drop(missing);
        let mut borrowed = capsule.borrow_for_workspace(&cwd.join("target")).unwrap();
        let mut next =
            Layout::from_originals(&workspace, None, "debug", true, true, &mut borrowed).unwrap();
        assert!(
            borrowed.is_empty(),
            "next actual Layout consumes the complete originals"
        );
        drop(capsule);
        probe(&paths, true);
        let guards = next.take_compile_leases().unwrap();
        drop(next);
        probe(&paths, true);
        drop(guards);
        probe(&paths, false);
    }

    #[test]
    fn next_layout_refusal_preserves_ordinary_guard_population_and_original_lock_custody() {
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        let (mut guards, paths) = actual_layout_guards(&cwd);
        let population = guards.len();
        // Actual duplicates of these ordinary descriptions make accidental
        // explicit LOCK_UN observable even while the copies remain live.
        let copies = guards
            .iter()
            .map(|guard| guard.file().try_clone().unwrap())
            .collect::<Vec<_>>();
        let mut context = GlobalContext::new(
            Shell::from_write(Box::new(Vec::<u8>::new())),
            cwd.clone(),
            cwd.join("cargo-home"),
        );
        context.set_env(Default::default());
        context.set_search_stop_path(&cwd);
        context
            .configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&cwd.join("Cargo.toml"), &context).unwrap();
        assert!(
            Layout::from_originals(&workspace, None, "debug", true, true, &mut guards).is_err()
        );
        probe(&paths, true);
        assert_eq!(
            guards.len(),
            population,
            "a refused borrow must leave the complete original Vec unchanged"
        );
        assert_eq!(
            guards
                .iter()
                .map(|guard| guard.path().to_owned())
                .collect::<Vec<_>>(),
            paths
        );
        drop(copies);
        probe(&paths, true);
        drop(guards);
        probe(&paths, false);
    }

    pub(super) fn actual_layout_guards(cwd: &Path) -> (Vec<FileLock>, Vec<std::path::PathBuf>) {
        std::fs::create_dir(cwd.join("src")).unwrap();
        std::fs::write(cwd.join("src/lib.rs"), "").unwrap();
        std::fs::write(
            cwd.join("Cargo.toml"),
            "[package]\nname='retained-output-ofd-fixture'\nversion='0.1.0'\n",
        )
        .unwrap();
        let mut context = GlobalContext::new(
            Shell::from_write(Box::new(Vec::<u8>::new())),
            cwd.to_owned(),
            cwd.join("cargo-home"),
        );
        context.set_env(Default::default());
        context.set_search_stop_path(cwd);
        context
            .configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&cwd.join("Cargo.toml"), &context).unwrap();
        let mut layout = Layout::new(&workspace, None, "debug", true, true).unwrap();
        let guards = layout.take_compile_leases().unwrap();
        let paths = guards.iter().map(|guard| guard.path().to_owned()).collect();
        drop(layout);
        (guards, paths)
    }

    #[test]
    fn retained_original_descriptions_exclude_writers_after_workload_normal_drop_or_unwind() {
        for unwind in [false, true] {
            let temporary = tempfile::tempdir().unwrap();
            let cwd = temporary.path().canonicalize().unwrap();
            let (guards, paths) = actual_layout_guards(&cwd);
            let capsule =
                OriginalOutputLeases::from_original_layouts(guards, &cwd.join("target")).unwrap();
            // Exact duplicates of the original descriptions, never new opens
            // or an independent lock acquisition from matching path data.
            let (offer, originals) = capsule
                .output_offer(
                    trust_resource_controller::workload::host::output::Key {
                        root_attempt: [1; 16],
                        invocation_sha256: [2; 32],
                        attempt: [3; 16],
                    },
                    &cwd.join("target"),
                )
                .unwrap();
            assert_eq!(offer.locks.len(), 3);
            assert_eq!(originals.len(), offer.locks.len());
            let original_copies = originals
                .iter()
                .map(|fd| std::fs::File::from(fd.try_clone_to_owned().unwrap()))
                .collect::<Vec<_>>();
            drop(originals);
            probe(&paths, true);
            if unwind {
                assert!(
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                        let _original = capsule;
                        panic!("owned workload unwinds");
                    }))
                    .is_err()
                );
            } else {
                drop(capsule);
            }
            probe(&paths, true);
            drop(original_copies);
            probe(&paths, false);
        }
    }

    #[test]
    fn ordinary_layout_guard_drop_keeps_its_existing_explicit_unlock_behavior() {
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        let (guards, paths) = actual_layout_guards(&cwd);
        let copies = guards
            .iter()
            .map(|guard| guard.file().try_clone().unwrap())
            .collect::<Vec<_>>();
        probe(&paths, true);
        drop(guards);
        probe(&paths, false);
        drop(copies);
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "isolated native owner-death actor chooses its fixture before configuration"
    )]
    fn same_original_lock_descriptions_survive_actual_owner_process_death() {
        use std::os::fd::{AsFd, AsRawFd, FromRawFd};
        use std::os::unix::net::{UnixListener, UnixStream};
        use std::time::{Duration, Instant};
        const SOCKET: &str = "TARGO_ORIGINAL_OUTPUT_LOCK_TEST_SOCKET";
        let deadline = Instant::now() + Duration::from_secs(15);
        if let Some(socket) = std::env::var_os(SOCKET) {
            let socket = std::path::PathBuf::from(socket);
            let root = socket.parent().unwrap().join("owner");
            std::fs::create_dir(&root).unwrap();
            let root = root.canonicalize().unwrap();
            let (guards, paths) = actual_layout_guards(&root);
            let capsule =
                OriginalOutputLeases::from_original_layouts(guards, &root.join("target")).unwrap();
            let stream = UnixStream::connect(&socket).unwrap();
            let mut channel =
                trust_resource_controller::Channel::new(stream.try_clone().unwrap()).unwrap();
            channel
                .send(&serde_json::to_vec(&paths).unwrap(), deadline)
                .unwrap();
            let originals = capsule
                .guards
                .iter()
                .map(|guard| guard.file().as_fd())
                .collect::<Vec<_>>();
            jobserver_utils::descriptor_transfer::send(&stream, &originals, 0x5b, deadline)
                .unwrap();
            // SAFETY: signal only this actual actor's current process. Park
            // until native delivery; no destructor or panic can run first.
            assert_eq!(unsafe { libc::kill(libc::getpid(), libc::SIGKILL) }, 0);
            loop {
                std::thread::park();
            }
        }
        struct Inputs {
            directory: Option<tempfile::TempDir>,
            complete: bool,
        }
        impl Drop for Inputs {
            fn drop(&mut self) {
                if !self.complete {
                    let kept = self.directory.take().unwrap().keep();
                    eprintln!("preserved original lock actor inputs: {}", kept.display());
                }
            }
        }
        let mut inputs = Inputs {
            directory: Some(tempfile::tempdir().unwrap()),
            complete: false,
        };
        let socket = inputs
            .directory
            .as_ref()
            .unwrap()
            .path()
            .join("original-locks.sock");
        let stderr_path = inputs
            .directory
            .as_ref()
            .unwrap()
            .path()
            .join("owner.stderr");
        let listener = UnixListener::bind(&socket).unwrap();
        listener.set_nonblocking(true).unwrap();
        struct Owner(Option<std::process::Child>);
        impl Drop for Owner {
            fn drop(&mut self) {
                if let Some(child) = self.0.as_mut() {
                    match child.try_wait() {
                        Ok(Some(_)) => {}
                        Ok(None) => {
                            let _ = child.kill();
                            let _ = child.wait();
                        }
                        Err(_) => {
                            let _ = child.wait();
                        }
                    }
                }
            }
        }
        let mut owner=Owner(Some(std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact","compiler::build_runner::workload_leases::tests::same_original_lock_descriptions_survive_actual_owner_process_death"])
            .env(SOCKET,&socket).stdout(std::process::Stdio::null()).stderr(std::fs::File::create(&stderr_path).unwrap()).spawn().unwrap()));
        let stream = loop {
            match listener.accept() {
                Ok((stream, _)) => break stream,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    assert!(
                        Instant::now() < deadline,
                        "native owner did not reach original handoff"
                    );
                    assert!(
                        owner.0.as_mut().unwrap().try_wait().unwrap().is_none(),
                        "native owner exited before handoff: {}",
                        std::fs::read_to_string(&stderr_path).unwrap_or_default()
                    );
                    std::thread::sleep(Duration::from_millis(1));
                }
                Err(error) => panic!("{error}"),
            }
        };
        let mut channel =
            trust_resource_controller::Channel::new(stream.try_clone().unwrap()).unwrap();
        let paths: Vec<std::path::PathBuf> =
            serde_json::from_slice(&channel.receive(deadline).unwrap()).unwrap();
        assert_eq!(
            paths.len(),
            3,
            "complete actual original Layout guard census"
        );
        let mut marker = [0u8];
        let mut control = [0usize; 512];
        let mut iov = libc::iovec {
            iov_base: marker.as_mut_ptr().cast(),
            iov_len: 1,
        };
        // SAFETY: zero initializes optional native pointers/counts below.
        let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
        message.msg_iov = &mut iov;
        message.msg_iovlen = 1;
        message.msg_control = control.as_mut_ptr().cast();
        message.msg_controllen = std::mem::size_of_val(&control) as _;
        let received = loop {
            assert!(
                Instant::now() < deadline,
                "original descriptions never arrived"
            );
            #[cfg(target_os = "linux")]
            let flags = libc::MSG_DONTWAIT | libc::MSG_CMSG_CLOEXEC;
            #[cfg(not(target_os = "linux"))]
            let flags = libc::MSG_DONTWAIT;
            // SAFETY: all iovec/ancillary storage remains live and bounded.
            let n = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut message, flags) };
            if n >= 0 {
                break n;
            }
            let error = std::io::Error::last_os_error();
            assert!(
                matches!(
                    error.kind(),
                    std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
                ),
                "{error}"
            );
            std::thread::sleep(Duration::from_millis(1));
            message.msg_controllen = std::mem::size_of_val(&control) as _;
        };
        let mut originals = Vec::new();
        // SAFETY: bounded initialized native ancillary buffer from our own
        // actual actor. Adopt every delivered right before asserting shape.
        unsafe {
            let mut header = libc::CMSG_FIRSTHDR(&message);
            while !header.is_null() {
                let length = (*header).cmsg_len as usize;
                let base = libc::CMSG_LEN(0) as usize;
                let remaining = message.msg_controllen as usize
                    - (header as usize - message.msg_control as usize);
                assert!(length >= base && length <= remaining);
                assert_eq!(
                    ((*header).cmsg_level, (*header).cmsg_type),
                    (libc::SOL_SOCKET, libc::SCM_RIGHTS)
                );
                assert_eq!((length - base) % std::mem::size_of::<libc::c_int>(), 0);
                let data = libc::CMSG_DATA(header).cast::<libc::c_int>();
                for index in 0..(length - base) / std::mem::size_of::<libc::c_int>() {
                    originals.push(std::fs::File::from_raw_fd(data.add(index).read_unaligned()));
                }
                header = libc::CMSG_NXTHDR(&message, header);
            }
        }
        assert_eq!(received, 1);
        assert_eq!(marker, [0x5b]);
        assert_eq!(message.msg_flags & (libc::MSG_CTRUNC | libc::MSG_TRUNC), 0);
        assert_eq!(originals.len(), paths.len());
        for (file, path) in originals.iter().zip(&paths) {
            use std::os::unix::fs::MetadataExt;
            let held = file.metadata().unwrap();
            let named = std::fs::metadata(path).unwrap();
            assert_eq!((held.dev(), held.ino()), (named.dev(), named.ino()));
            // SAFETY: only local inheritance flags of our received copy.
            let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
            assert!(flags >= 0);
            assert_eq!(
                unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) },
                0
            );
        }
        loop {
            if let Some(status) = owner.0.as_mut().unwrap().try_wait().unwrap() {
                use std::os::unix::process::ExitStatusExt;
                assert_eq!(status.signal(), Some(libc::SIGKILL));
                break;
            }
            assert!(Instant::now() < deadline, "original owner did not exit");
            std::thread::sleep(Duration::from_millis(1));
        }
        owner.0.take();
        probe(&paths, true);
        drop(originals);
        probe(&paths, false);
        inputs.complete = true;
    }
    #[test]
    fn moved_compile_leases_exclude_real_child_writers_until_capsule_drop_and_detect_path_substitution()
     {
        let temporary = tempfile::tempdir().unwrap();
        let cwd = temporary.path().canonicalize().unwrap();
        std::fs::create_dir(cwd.join("src")).unwrap();
        std::fs::write(cwd.join("src/lib.rs"), "").unwrap();
        std::fs::write(
            cwd.join("Cargo.toml"),
            "[package]\nname='original-output-lease-fixture'\nversion='0.1.0'\n",
        )
        .unwrap();
        let mut context = GlobalContext::new(
            Shell::from_write(Box::new(Vec::<u8>::new())),
            cwd.clone(),
            cwd.join("cargo-home"),
        );
        context.set_env(Default::default());
        context.set_search_stop_path(&cwd);
        context
            .configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&cwd.join("Cargo.toml"), &context).unwrap();
        let root = workspace.target_dir().into_path_unlocked();
        let mut layout = Layout::new(&workspace, None, "debug", true, true).unwrap();
        let guards = layout.take_compile_leases().unwrap();
        let paths = guards
            .iter()
            .map(|guard| guard.path().to_owned())
            .collect::<Vec<_>>();
        let capsule = std::sync::Arc::new(
            OriginalOutputLeases::from_original_layouts(guards, &root).unwrap(),
        );
        // Actual concurrent compilation/intermediate/final capsules retain
        // ONE original FileLock owner, never duplicated lock descriptions.
        let intermediate = std::sync::Arc::clone(&capsule);
        let final_outputs = std::sync::Arc::clone(&capsule);
        assert!(std::sync::Arc::ptr_eq(&capsule, &intermediate));
        assert!(std::sync::Arc::ptr_eq(&capsule, &final_outputs));
        layout.release_compile_leases();
        drop(layout);
        probe(&paths, true);
        let changed = &paths[2];
        let old = changed.with_extension("held-original");
        std::fs::rename(changed, &old).unwrap();
        std::fs::File::create(changed)
            .unwrap()
            .write_all(b"replacement")
            .unwrap();
        assert!(capsule.validate(&root).is_err());
        std::fs::remove_file(changed).unwrap();
        std::fs::rename(&old, changed).unwrap();
        capsule.validate(&root).unwrap();
        probe(&paths, true);
        drop(capsule);
        probe(&paths, true);
        drop(final_outputs);
        probe(&paths, true);
        intermediate.validate(&root).unwrap();
        drop(intermediate);
        probe(&paths, false);
    }
}

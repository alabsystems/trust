//! Explicit live-machine qualification of ONE independently selected normal
//! Targo image. This creates no private CPU domain or completed-runtime fixture.

use std::os::fd::AsRawFd as _;
use std::os::unix::fs::MetadataExt as _;
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::thread::JoinHandle;
use std::time::Instant;

use super::super::super::{Acquire, LeaseAcquisition, Manager, process};
use super::*;

fn selected(name: &str) -> HeldSystemCommand {
    let path =
        PathBuf::from(std::env::var_os(format!("{name}_IMAGE")).expect("select actual image"));
    let expected = std::env::var(format!("{name}_SHA256")).expect("select actual image digest");
    let image = HeldSystemCommand::open(&path, input_deadline().unwrap()).unwrap();
    assert_eq!(image.observation().executable.sha256, expected);
    image
}

fn request(purpose: &str) -> Acquire {
    Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: purpose.to_owned(),
        contract: "actual public native child qualification".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    }
}

fn original(manager: &Manager, purpose: &str) -> super::super::super::Lease {
    // This is another namespace handle, not a copied lease. The consuming
    // acquisition still obtains exactly one actual original fixture owner.
    match Manager::open(&manager.root.physical).unwrap().acquire_lease(&request(purpose)).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("owned fixture unexpectedly busy"),
    }
}

struct World(PathBuf);
impl World {
    fn path(&self) -> &Path {
        &self.0
    }
}

fn world(name: &str) -> World {
    let destination = PathBuf::from(
        std::env::var_os("TRUST_NATIVE_PUBLIC_ARTIFACT_ROOT")
            .expect("select the private retained public-control artifact root"),
    );
    assert!(destination.is_absolute());
    std::fs::create_dir_all(&destination).unwrap();
    let path = tempfile::Builder::new().prefix(name).tempdir_in(destination).unwrap().keep();
    let path = std::fs::canonicalize(path).unwrap();
    println!("retained public-control world={}", path.display());
    World(path)
}

fn root() -> World {
    let root = world("root-");
    let status =
        Command::new("/usr/bin/git").args(["init", "--quiet"]).arg(root.path()).status().unwrap();
    assert!(status.success());
    root
}

struct Output {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

struct PublicChild {
    child: std::process::Child,
    stdout: Option<JoinHandle<Vec<u8>>>,
    stderr: Option<JoinHandle<Vec<u8>>>,
    reaped: bool,
}

impl PublicChild {
    fn start(
        targo: &HeldSystemCommand,
        bootstrap: &Path,
        root: &Path,
        scheduler: &Jobserver,
        args: &[OsString],
    ) -> Self {
        let mut command = Command::new(targo.program());
        command
            .current_dir(root)
            .args([
                "--unverified",
                "resource",
                "fixed",
                "--cpus",
                "1",
                "--memory-mib",
                "2048",
                "--wait-seconds",
                "60",
                "--",
                "repo-lock-exec",
                "--repo-root",
            ])
            .arg(root)
            .args(["--purpose", "actual native public exec control", "--"])
            .arg(bootstrap)
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        scheduler.configure_make(&mut command);
        targo.validate(input_deadline().unwrap()).unwrap();
        let mut child = command.spawn().unwrap();
        fn reader(
            mut stream: impl io::Read + std::os::fd::AsRawFd + Send + 'static,
        ) -> JoinHandle<Vec<u8>> {
            std::thread::spawn(move || {
                let mut bytes = Vec::new();
                let deadline = Instant::now() + Duration::from_secs(120);
                loop {
                    assert!(Instant::now() < deadline, "actual public stream never reached EOF");
                    let mut observed =
                        libc::pollfd { fd: stream.as_raw_fd(), events: libc::POLLIN, revents: 0 };
                    let ready = unsafe { libc::poll(&mut observed, 1, 50) };
                    if ready < 0 {
                        let error = io::Error::last_os_error();
                        if error.kind() == io::ErrorKind::Interrupted {
                            continue;
                        }
                        panic!("actual stream poll failed: {error}");
                    }
                    if ready == 0 {
                        continue;
                    }
                    let mut chunk = [0; 8192];
                    match stream.read(&mut chunk) {
                        Ok(0) => break,
                        Ok(count) => bytes.extend_from_slice(&chunk[..count]),
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(error) => panic!("actual stream read failed: {error}"),
                    }
                    assert!(bytes.len() <= 1024 * 1024, "public diagnostic exceeds capture bound");
                }
                bytes
            })
        }
        let stdout = Some(reader(child.stdout.take().unwrap()));
        let stderr = Some(reader(child.stderr.take().unwrap()));
        Self { child, stdout, stderr, reaped: false }
    }

    fn terminate(&self) {
        // The actual outer native owner forwards this to its original group.
        // The fixture never signals a caller-selected group or another owner.
        assert_eq!(unsafe { libc::kill(self.child.id() as i32, libc::SIGTERM) }, 0);
    }

    fn finish(mut self) -> Output {
        let deadline = Instant::now() + Duration::from_secs(90);
        let status = loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                self.reaped = true;
                break status;
            }
            assert!(Instant::now() < deadline, "actual public native owner did not finish");
            std::thread::sleep(Duration::from_millis(10));
        };
        Output {
            status,
            stdout: self.stdout.take().unwrap().join().unwrap(),
            stderr: self.stderr.take().unwrap().join().unwrap(),
        }
    }

    fn actual_bootstrap(
        &mut self,
        manager: &Manager,
        image: &Path,
        blocked: &Manager,
    ) -> process::Process {
        let original =
            std::fs::metadata(blocked.root.physical.join(super::super::super::HOLDER).join("info"))
                .unwrap();
        let deadline = Instant::now() + Duration::from_secs(70);
        loop {
            assert!(self.child.try_wait().unwrap().is_none(), "public owner exited before child");
            if let Some(holder) = manager.status().unwrap().holder {
                for pid in process::all_pids().unwrap() {
                    let Ok(child) = process::read(pid) else { continue };
                    if child.parent == holder.pid
                        && !child.zombie
                        && process::args(pid).ok().and_then(|v| v.first().cloned()).as_deref()
                            == Some(image.as_os_str())
                        && observes_original_record(child.pid, &original)
                    {
                        assert_eq!(process::read(child.pid).unwrap().birth, child.birth);
                        return child;
                    }
                }
            }
            assert!(Instant::now() < deadline, "actual supported Bootstrap did not start");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

fn observes_original_record(pid: u32, expected: &std::fs::Metadata) -> bool {
    // Readiness DATA only: this original child has actually entered its normal
    // Manager acquisition, beyond dyld and the suspended launch. This observes
    // an original record vnode, never its contents/lock state/release authority.
    #[repr(C)]
    struct FileInfo {
        flags: u32,
        status: u32,
        offset: i64,
        kind: i32,
        guards: u32,
    }
    #[repr(C)]
    struct VnodeWithPath {
        file: FileInfo,
        vnode: libc::vnode_info_path,
    }
    const {
        assert!(std::mem::size_of::<FileInfo>() == 24);
    }
    let size = std::mem::size_of::<libc::proc_fdinfo>();
    let mut fds = vec![0_u8; 4096 * size];
    // SAFETY: bounded writable FD census for our identified live child.
    let count = unsafe {
        libc::proc_pidinfo(
            pid as i32,
            libc::PROC_PIDLISTFDS,
            0,
            fds.as_mut_ptr().cast(),
            fds.len() as i32,
        )
    };
    if count <= 0 || count as usize >= fds.len() || !(count as usize).is_multiple_of(size) {
        return false;
    }
    for bytes in fds[..count as usize].chunks_exact(size) {
        // SAFETY: successful complete public proc_fdinfo row, no alignment assumption.
        let entry = unsafe { std::ptr::read_unaligned(bytes.as_ptr().cast::<libc::proc_fdinfo>()) };
        if entry.proc_fdtype != libc::PROX_FDTYPE_VNODE as u32 {
            continue;
        }
        let mut observed = std::mem::MaybeUninit::<VnodeWithPath>::zeroed();
        let length = std::mem::size_of::<VnodeWithPath>() as i32;
        // SAFETY: exact public proc_info.h vnode_fdinfowithpath structure.
        let got = unsafe {
            libc::proc_pidfdinfo(pid as i32, entry.proc_fd, 2, observed.as_mut_ptr().cast(), length)
        };
        if got == length {
            let observed = unsafe { observed.assume_init() };
            let stat = observed.vnode.vip_vi.vi_stat;
            if stat.vst_dev == expected.dev() as u32 && stat.vst_ino == expected.ino() {
                return true;
            }
        }
    }
    false
}

impl Drop for PublicChild {
    fn drop(&mut self) {
        if !self.reaped {
            let _ = unsafe { libc::kill(self.child.id() as i32, libc::SIGTERM) };
            // Keep the original GNU fixture alive until its actual outer owner
            // has reaped/settled. No timeout fabricates original group closure.
            if self.child.wait().is_ok() {
                self.reaped = true;
            }
        }
        if let Some(reader) = self.stdout.take() {
            let _ = reader.join();
        }
        if let Some(reader) = self.stderr.take() {
            let _ = reader.join();
        }
    }
}

fn conserved(manager: &Manager, scheduler: &Jobserver, flags: [i32; 2]) {
    // A canceled inner owner may leave its ordinary stale record. Recovery is
    // the existing native observation path after actual outer retirement.
    let lease = original(manager, "post-retirement fixture conservation");
    lease.check_current().unwrap();
    drop(lease);
    assert!(manager.status().unwrap().is_free());
    assert_eq!(scheduler.client().available().unwrap(), 3);
    assert_eq!(
        scheduler
            .pipe_descriptors()
            .unwrap()
            .each_ref()
            .map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) }),
        flags
    );
}

fn wait_args(root: &Path) -> Vec<OsString> {
    words(&["--trust-build-tree-lock", "acquire", "--kind", "build", "--pid"])
        .into_iter()
        .chain([
            std::process::id().to_string().into(),
            "--wait".into(),
            "60".into(),
            "--repo-root".into(),
            root.as_os_str().to_owned(),
        ])
        .collect()
}

#[test]
#[ignore = "explicit actual canonical admission; select immutable Targo, supported Bootstrap and old Bootstrap images; run outside retained build-slot"]
fn actual_public_native_exec_preserves_status_cancel_original_inputs_and_resources() {
    assert!(std::env::var_os("BUILD_SLOT_HELD").is_none(), "run outside compiler admission");
    assert!(std::env::var_os("TRUST_BUILD_LOCK_TOKEN").is_none(), "no inherited fixture owner");
    let targo = selected("TRUST_NATIVE_PUBLIC_TARGO");
    let bootstrap = selected("TRUST_NATIVE_PUBLIC_BOOTSTRAP");
    let old = selected("TRUST_NATIVE_PUBLIC_OLD_BOOTSTRAP");
    bootstrap
        .require_bootstrap_fixed_protocol(
            &crate::bootstrap_protocol::BOOTSTRAP_FIXED_PROTOCOL_MARKER,
            input_deadline().unwrap(),
        )
        .unwrap();
    assert!(
        old.require_bootstrap_fixed_protocol(
            &crate::bootstrap_protocol::BOOTSTRAP_FIXED_PROTOCOL_MARKER,
            input_deadline().unwrap(),
        )
        .is_err()
    );
    let fixture = root();
    let manager = Manager::open(fixture.path()).unwrap();
    let scheduler = Jobserver::new(4).unwrap();
    scheduler.client().acquire_raw().unwrap();
    let flags = scheduler
        .pipe_descriptors()
        .unwrap()
        .each_ref()
        .map(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) });

    let help = PublicChild::start(
        &targo,
        bootstrap.program(),
        fixture.path(),
        &scheduler,
        &words(&["--help"]),
    )
    .finish();
    assert!(help.status.success(), "{}", String::from_utf8_lossy(&help.stderr));
    assert!(!help.stdout.is_empty());
    conserved(&manager, &scheduler, flags);
    println!("case=success actual_outer_code=0 original_gnu_remaining=3 tree_free=true");

    let failed = PublicChild::start(
        &targo,
        bootstrap.program(),
        fixture.path(),
        &scheduler,
        &words(&["--native-exec-deliberately-invalid-option"]),
    )
    .finish();
    assert_eq!(failed.status.code(), Some(2), "{}", String::from_utf8_lossy(&failed.stderr));
    conserved(&manager, &scheduler, flags);
    println!("case=nonzero actual_outer_code=2 original_gnu_remaining=3 tree_free=true");

    let unsupported =
        PublicChild::start(&targo, old.program(), fixture.path(), &scheduler, &words(&["--help"]))
            .finish();
    assert!(!unsupported.status.success());
    assert!(String::from_utf8_lossy(&unsupported.stderr).contains("does not declare"));
    conserved(&manager, &scheduler, flags);
    println!("case=old-image refused=true original_gnu_remaining=3 tree_free=true");

    let blocker = world("blocked-");
    let blocked_manager = Manager::open(blocker.path()).unwrap();
    let held = original(&blocked_manager, "block real child for cancellation");
    let mut canceled = PublicChild::start(
        &targo,
        bootstrap.program(),
        fixture.path(),
        &scheduler,
        &wait_args(blocker.path()),
    );
    let actual = canceled.actual_bootstrap(&manager, bootstrap.program(), &blocked_manager);
    assert_eq!(process::read(actual.pid).unwrap().birth, actual.birth);
    canceled.terminate();
    let canceled = canceled.finish();
    assert_eq!(canceled.status.code(), Some(128 + libc::SIGTERM));
    assert!(process::writer_gone(actual.pid).unwrap());
    drop(held);
    conserved(&manager, &scheduler, flags);
    println!("case=cancel actual_outer_code=143 original_gnu_remaining=3 tree_free=true");

    let images = world("images-");
    let copy = images.path().join("bootstrap");
    std::fs::copy(bootstrap.program(), &copy).unwrap();
    let copy = std::fs::canonicalize(copy).unwrap();
    let copied = HeldSystemCommand::open(&copy, input_deadline().unwrap()).unwrap();
    assert_eq!(copied.observation().executable.sha256, bootstrap.observation().executable.sha256);
    let held = original(&blocked_manager, "block real child before final input failure");
    let mut unknown =
        PublicChild::start(&targo, &copy, fixture.path(), &scheduler, &wait_args(blocker.path()));
    let actual = unknown.actual_bootstrap(&manager, &copy, &blocked_manager);
    std::fs::rename(&copy, images.path().join("retired-bootstrap")).unwrap();
    drop(held);
    let unknown = unknown.finish();
    assert!(!unknown.status.success());
    let error = String::from_utf8_lossy(&unknown.stderr);
    assert!(error.contains("actual child exit status: 0"), "{error}");
    assert!(error.contains("original input recheck failed"), "{error}");
    assert!(process::writer_gone(actual.pid).unwrap());
    // The real administrative child named THIS live fixture as its holder.
    // Retire only that actual ordinary operation, never a WITHHELD record.
    let holder = blocked_manager.status().unwrap().holder.unwrap();
    assert_eq!(holder.pid, std::process::id());
    assert!(!holder.is_withheld());
    assert_eq!(
        blocked_manager.release(&holder.token).unwrap(),
        super::super::super::Release::Released
    );
    conserved(&manager, &scheduler, flags);
    println!("case=input-unknown actual_child_exit=0 original_gnu_remaining=3 tree_free=true");
    targo.validate(input_deadline().unwrap()).unwrap();
    bootstrap.validate(input_deadline().unwrap()).unwrap();
    println!(
        "actual public success/nonzero/old-image/cancel/input-Unknown and original GNU/tree conservation passed; no runtime-session or SDK claim"
    );
}

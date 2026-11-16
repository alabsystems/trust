//! Private early role in the SAME native Targo image, never a helper binary.
//! It narrows itself before loading the selected compiler and creates no job.

use std::collections::BTreeMap;
use std::ffi::CString;
use std::os::fd::FromRawFd as _;
use std::os::unix::ffi::OsStrExt as _;

use super::*;

pub(super) const ENTRY: &str = "--native-cache-version-prelude-v1";
pub(super) const ACK: u8 = 0x6d;
pub(super) const EXEC: u8 = 0x7c;
const MAX_PLAN: usize = 128 * 1024;

#[derive(serde_derive::Serialize, serde_derive::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Plan {
    parent_pid: u32,
    parent_birth: u64,
    parent_unique: u64,
    parent_exec: u32,
    program: Vec<u8>,
    runtime: Vec<(Vec<u8>, Vec<u8>)>,
}
impl Plan {
    pub(super) fn new(program: &HeldProgram) -> io::Result<Self> {
        let parent = process::read_identity(std::process::id())?;
        Ok(Self {
            parent_pid: parent.pid,
            parent_birth: parent.birth,
            parent_unique: parent.unique_id,
            parent_exec: parent.exec_version,
            program: program.program().as_os_str().as_bytes().to_vec(),
            runtime: program
                .runtime_environment()?
                .into_iter()
                .map(|(n, v)| (n.as_bytes().to_vec(), v.as_bytes().to_vec()))
                .collect(),
        })
    }
}
fn time(until: Instant) -> io::Result<()> {
    if Instant::now() >= until { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn write(stream: &mut UnixStream, mut bytes: &[u8], until: Instant) -> io::Result<()> {
    while !bytes.is_empty() {
        time(until)?;
        match stream.write(bytes) {
            Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
            Ok(n) => bytes = &bytes[n..],
            Err(e)
                if matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) =>
            {
                std::thread::sleep(POLL)
            }
            Err(e) => return Err(e),
        }
    }
    time(until)
}
fn read(stream: &mut UnixStream, mut bytes: &mut [u8], until: Instant) -> io::Result<()> {
    while !bytes.is_empty() {
        time(until)?;
        match stream.read(bytes) {
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => bytes = &mut bytes[n..],
            Err(e)
                if matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) =>
            {
                std::thread::sleep(POLL)
            }
            Err(e) => return Err(e),
        }
    }
    time(until)
}
pub(super) fn send_plan(stream: &mut UnixStream, plan: &Plan, until: Instant) -> io::Result<()> {
    let bytes = serde_json::to_vec(plan).map_err(io::Error::other)?;
    if bytes.len() > MAX_PLAN {
        return Err(invalid("cache version plan exceeds bound"));
    }
    write(stream, &(bytes.len() as u32).to_be_bytes(), until)?;
    write(stream, &bytes, until)
}
pub(super) fn loader(name: &OsStr) -> bool {
    name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_")
}

pub(super) fn no_fork(pid: u32) -> io::Result<bool> {
    unsafe extern "C" {
        fn sandbox_check(pid: i32, operation: *const libc::c_char, kind: i32, ...) -> i32;
    }
    let pid = i32::try_from(pid).map_err(|_| invalid("invalid native no-fork subject"))?;
    match unsafe { sandbox_check(pid, c"process-fork".as_ptr(), 0) } {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(invalid("native no-fork observation unavailable")),
    }
}
pub(super) fn no_escape(original: Identity) -> io::Result<()> {
    let pid = i32::try_from(original.pid).map_err(|_| invalid("invalid confined probe PID"))?;
    if process::read_identity(original.pid)? != original
        || unsafe { libc::getsid(pid) } != pid
        || unsafe { libc::getpgid(pid) } != pid
        || !no_fork(original.pid)?
        || process::read_identity(original.pid)? != original
    {
        return Err(invalid("original cache probe lost actual no-fork session leadership"));
    }
    Ok(())
}

pub(super) fn install() -> io::Result<()> {
    unsafe extern "C" {
        fn sandbox_init(
            profile: *const libc::c_char,
            flags: u64,
            error: *mut *mut libc::c_char,
        ) -> i32;
        fn sandbox_free_error(error: *mut libc::c_char);
    }
    let mut error = std::ptr::null_mut();
    // SAFETY: private early single-process role, static restrictive policy;
    // never a pre_exec callback after a multithreaded fork.
    let result = unsafe {
        sandbox_init(c"(version 1)(allow default)(deny process-fork)".as_ptr(), 0, &mut error)
    };
    if !error.is_null() {
        unsafe {
            sandbox_free_error(error);
        }
    }
    if result != 0 || !no_fork(std::process::id())? {
        return Err(invalid("native cache no-fork installation refused"));
    }
    Ok(())
}

/// Call at original main entry before GNU/SDK import, logging, callbacks or
/// threads. An unselected invocation performs no descriptor operation. The
/// role only installs restrictions and executes exact --version; it grants no
/// resource/Manager/output/SDK authority from this flag, plan or peer image.
pub fn private_entry(args: impl IntoIterator<Item = OsString>) -> Option<i32> {
    let mut args = args.into_iter();
    if args.next().as_deref() != Some(OsStr::new(ENTRY)) {
        return None;
    }
    let mut run = || -> io::Result<()> {
        let control = args
            .next()
            .and_then(|a| a.into_string().ok())
            .and_then(|a| a.strip_prefix("--control-fd=").and_then(|s| s.parse::<i32>().ok()))
            .filter(|fd| *fd >= 3)
            .ok_or_else(|| invalid("invalid cache prelude original control"))?;
        if args.next().is_some() {
            return Err(invalid("cache prelude accepts only its original control"));
        }
        for name in [
            "ATERM_RESOURCE_JOB_V3",
            "ATERM_SDK_LEASE_V3",
            "TRUST_RESOURCE_ROOT_FD",
            "TRUST_BOOTSTRAP_HOST_STORE_FD",
        ] {
            if std::env::var_os(name).is_some() {
                return Err(invalid("cache prelude cannot replace an inherited hosted/SDK role"));
            }
        }
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // Observe the original inherited target before any library can open a
        // descriptor and reuse a closed target. Never repair a missing slot.
        if unsafe { libc::fstat(control, stat.as_mut_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if unsafe { stat.assume_init() }.st_mode & libc::S_IFMT != libc::S_IFSOCK {
            return Err(invalid("cache prelude control is not a socket"));
        }
        install()?;
        let mut channel = unsafe { UnixStream::from_raw_fd(control) };
        channel.set_nonblocking(true)?;
        let until = deadline()?;
        let parent = process::read_identity(unsafe { libc::getppid() } as u32)?;
        process::check_peer(&channel, parent)?;
        let same_image = HeldSystemCommand::open(&std::env::current_exe()?, until)?;
        same_image.validate_loaded(parent, until)?;
        let mut length = [0; 4];
        read(&mut channel, &mut length, until)?;
        let length = u32::from_be_bytes(length) as usize;
        if length == 0 || length > MAX_PLAN {
            return Err(invalid("invalid cache prelude plan length"));
        }
        let mut bytes = vec![0; length];
        read(&mut channel, &mut bytes, until)?;
        let plan: Plan = serde_json::from_slice(&bytes).map_err(io::Error::other)?;
        if (plan.parent_pid, plan.parent_birth, plan.parent_unique, plan.parent_exec)
            != (parent.pid, parent.birth, parent.unique_id, parent.exec_version)
            || !Path::new(OsStr::from_bytes(&plan.program)).is_absolute()
            || plan.runtime.len() > 1
            || plan
                .runtime
                .iter()
                .any(|(n, v)| n != b"DYLD_LIBRARY_PATH" || v.is_empty() || v.contains(&0))
            || std::env::vars_os().any(|(n, _)| loader(&n))
        {
            return Err(invalid("cache prelude plan differs from its original closed controller"));
        }
        process::check_peer(&channel, parent)?;
        let flags = unsafe { libc::fcntl(control, libc::F_GETFD) };
        if flags < 0
            || unsafe { libc::fcntl(control, libc::F_SETFD, flags | libc::FD_CLOEXEC) } != 0
        {
            return Err(io::Error::last_os_error());
        }
        write(&mut channel, &[ACK], until)?;
        // The parent independently observes actual no-fork before this second
        // instruction. The byte alone is never a confinement/CPU capability.
        let mut go = [0];
        read(&mut channel, &mut go, until)?;
        if go != [EXEC] {
            return Err(invalid("invalid original cache exec instruction"));
        }
        process::check_peer(&channel, parent)?;
        same_image.validate_loaded(parent, until)?;
        if !no_fork(std::process::id())? {
            return Err(invalid("cache prelude lost no-fork policy"));
        }
        // Native launch made this SAME child a dedicated session leader.
        // A session leader cannot setsid/setpgid away, and no-fork prevents
        // creating a nonleader escape child. The parent independently checks
        // these same kernel facts before target GO and original closure.
        no_escape(process::read_identity(std::process::id())?)?;
        exec_version(plan, until)
    };
    Some(match run() {
        Ok(()) => 75,
        Err(e) => {
            let _ = writeln!(io::stderr().lock(), "native cache version prelude: {e}");
            75
        }
    })
}
fn exec_version(plan: Plan, until: Instant) -> io::Result<()> {
    let program = CString::new(plan.program).map_err(io::Error::other)?;
    let version = c"--version";
    let argv = [program.as_ptr().cast_mut(), version.as_ptr().cast_mut(), std::ptr::null_mut()];
    let mut environment: BTreeMap<OsString, OsString> = std::env::vars_os().collect();
    // This is a confined version child, not an independently admitted resource
    // root. The parent retains the actual fixed owner. Its direct/courier
    // locators name descriptors deliberately not exported to this child and
    // must not advertise closed/reused slots to the compiler's early entry.
    environment.remove(OsStr::new(super::super::FIXED_HANDOFF_ENV));
    environment.remove(OsStr::new(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV));
    environment.remove(OsStr::new("BUILD_SLOT_HELD"));
    for (n, v) in plan.runtime {
        environment.insert(OsStr::from_bytes(&n).to_owned(), OsStr::from_bytes(&v).to_owned());
    }
    let environment = environment
        .into_iter()
        .map(|(n, v)| {
            let mut bytes = n.as_bytes().to_vec();
            bytes.push(b'=');
            bytes.extend(v.as_bytes());
            CString::new(bytes).map_err(io::Error::other)
        })
        .collect::<io::Result<Vec<_>>>()?;
    let mut envp = environment.iter().map(|s| s.as_ptr().cast_mut()).collect::<Vec<_>>();
    envp.push(std::ptr::null_mut());
    let mut attr = std::mem::MaybeUninit::<libc::posix_spawnattr_t>::uninit();
    let checked = |code| if code == 0 { Ok(()) } else { Err(io::Error::from_raw_os_error(code)) };
    unsafe {
        checked(libc::posix_spawnattr_init(attr.as_mut_ptr()))?;
    }
    let mut attr = unsafe { attr.assume_init() };
    let result = (|| {
        unsafe {
            checked(libc::posix_spawnattr_setflags(
                &mut attr,
                (libc::POSIX_SPAWN_SETEXEC | libc::POSIX_SPAWN_START_SUSPENDED) as libc::c_short,
            ))?;
        }
        time(until)?;
        let mut pid = 0;
        // SETEXEC replaces this SAME confined process, without a fork/helper,
        // and suspends the loaded target before its first user instruction.
        unsafe {
            checked(libc::posix_spawn(
                &mut pid,
                program.as_ptr(),
                std::ptr::null(),
                &attr,
                argv.as_ptr(),
                envp.as_ptr(),
            ))?;
        }
        Err(invalid("cache suspended exec unexpectedly returned"))
    })();
    unsafe {
        libc::posix_spawnattr_destroy(&mut attr);
    }
    result
}

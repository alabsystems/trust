//! Native observations of an existing process, never child/control authority.

use super::*;
use crate::trust_repo_lock::management::process;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct Identity {
    pub(super) pid: u32,
    pub(super) uid: u32,
    pub(super) birth: String,
    pub(super) executable: PathBuf,
}

pub(super) fn checked(pid: u32, cwd: &Directory) -> io::Result<Identity> {
    if pid == 0 || pid > i32::MAX as u32 {
        return Err(invalid("adoption requires an actual positive native PID"));
    }
    cwd.check()?;
    let before = process::read(pid)?;
    if before.zombie || before.uid != unsafe { libc::geteuid() } {
        return Err(invalid("adoption requires a live process of the same account"));
    }
    let birth = process::live_adoption_birth(pid)?
        .ok_or_else(|| invalid("adoption process already exited"))?;
    let image = executable(pid)?;
    if fs::canonicalize(process::cwd(pid)?)? != cwd.path {
        return Err(invalid("adoption requires the direct process's exact working directory"));
    }
    let after = process::read(pid)?;
    if before != after
        || executable(pid)? != image
        || process::live_adoption_birth(pid)?.as_deref() != Some(birth.as_str())
        || fs::canonicalize(process::cwd(pid)?)? != cwd.path
    {
        return Err(invalid("process changed during adoption identity observation"));
    }
    cwd.check()?;
    Ok(Identity { pid, uid: before.uid, birth, executable: image })
}

#[cfg(target_os = "macos")]
fn executable(pid: u32) -> io::Result<PathBuf> {
    // Public libproc.h + sys/proc_info.h: PROC_PIDPATHINFO_MAXSIZE=4*MAXPATHLEN.
    // Apple's wrapper returns strlen on success and zero on failure. Zero is
    // an error, never a gone process; only the native birth/liveness reader may
    // classify that observation. No argv, helper, path reopen or task port.
    let mut bytes = [0_u8; 4096];
    let errno = unsafe { libc::__error() };
    unsafe {
        *errno = 0;
    }
    let count =
        unsafe { libc::proc_pidpath(pid as i32, bytes.as_mut_ptr().cast(), bytes.len() as u32) };
    let error = unsafe { *errno };
    if count <= 0 {
        return Err(if error == 0 {
            invalid("native executable path is unavailable")
        } else {
            io::Error::from_raw_os_error(error)
        });
    }
    let count = count as usize;
    if count >= bytes.len() || bytes[count] != 0 || bytes[..count].contains(&0) {
        return Err(invalid("native executable path is incomplete"));
    }
    let path = PathBuf::from(std::ffi::OsString::from_vec(bytes[..count].to_vec()));
    if !path.is_absolute() {
        return Err(invalid("native executable path is not absolute"));
    }
    Ok(path)
}

#[cfg(target_os = "linux")]
fn executable(pid: u32) -> io::Result<PathBuf> {
    let path = fs::read_link(format!("/proc/{pid}/exe"))?;
    validate_path(&path)?;
    Ok(path)
}

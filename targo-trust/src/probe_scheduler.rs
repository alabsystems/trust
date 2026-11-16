//! One owned scheduler for the fixed compiler capability query; no proof authority.
use std::process::{Command, Output};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::sync::OnceLock;
use std::time::Duration;

#[cfg(any(target_os = "linux", target_os = "macos"))]
use trust_resource_controller::client::probe_scheduler::ProbeScheduler;
#[cfg(any(target_os = "linux", target_os = "macos"))]
static CAPTURED: OnceLock<Result<ProbeScheduler, String>> = OnceLock::new();

// Libtest never enters native main. Only explicitly declared owned fake
// compilers may use the capture-only test seam; real commands still require
// native-entry custody. The scoped guard cannot move to another thread.
#[cfg(all(test, unix))]
std::thread_local! {
    static FAKE_COMPILER: std::cell::RefCell<Option<std::path::PathBuf>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(all(test, unix))]
pub(crate) struct FakeCompilerGuard {
    previous: Option<std::path::PathBuf>,
    _same_thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

#[cfg(all(test, unix))]
pub(crate) fn fake_compiler_for_test(path: &std::path::Path) -> FakeCompilerGuard {
    assert!(path.is_absolute(), "fake compiler must have an exact absolute path");
    assert!(std::fs::symlink_metadata(path).expect("owned fake compiler").file_type().is_file());
    let previous = FAKE_COMPILER.with(|slot| slot.replace(Some(path.to_path_buf())));
    FakeCompilerGuard { previous, _same_thread: std::marker::PhantomData }
}

#[cfg(all(test, unix))]
impl Drop for FakeCompilerGuard {
    fn drop(&mut self) {
        FAKE_COMPILER.with(|slot| slot.replace(self.previous.take()));
    }
}

/// # Safety
/// Must be the first native-main operation, before any file/worker/callback.
pub(crate) unsafe fn capture_at_entry() -> Result<(), String> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        // SAFETY: the caller promises original startup descriptors.
        let value = unsafe { ProbeScheduler::capture_at_entry() }.map_err(|e| e.to_string());
        CAPTURED.set(value).map_err(|_| "probe scheduler captured twice".to_string())?;
        CAPTURED.get().expect("set above").as_ref().map(|_| ()).map_err(Clone::clone)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    Ok(())
}

pub(crate) fn output(
    command: &mut Command,
    context: &str,
    limit: usize,
    timeout: Duration,
) -> Result<Output, String> {
    let capture =
        |command: &mut Command| crate::bounded_process::output(command, context, limit, timeout);
    #[cfg(all(test, unix))]
    if FAKE_COMPILER.with(|slot| {
        slot.borrow().as_ref().is_some_and(|path| command.get_program() == path.as_os_str())
    }) {
        return capture(command);
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        let scheduler = CAPTURED
            .get()
            .ok_or("probe scheduler not captured at native entry")?
            .as_ref()
            .map_err(Clone::clone)?;
        scheduler.with_command(command, capture).map_err(|e| e.to_string())?
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    capture(command)
}

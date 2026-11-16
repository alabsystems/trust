// Trust: one registered host child receives existing scheduling capabilities.
use super::*;

pub(super) enum Scope {
    Unbound,
    Failed,
    Bound(Process),
}

/// An inert endpoint armed once for one actual custodian-owned child.
///
/// Create before spawn, bind while the registered child is held before GO,
/// and retain through its completion. This transfers existing descriptors;
/// it never creates credits or proves host memory/subgroup registration.
/// Clones retain the SAME endpoint and one-use bind/failure state.
#[derive(Clone, Debug)]
pub struct ScopedHandoff(pub(super) Arc<Endpoint>);

impl ScopedHandoff {
    /// Serve an existing GNU pair using the recipient's target descriptor
    /// numbers, which must also appear in that child's MAKEFLAGS. The source
    /// descriptors may have entirely different numbers in the custodian.
    pub fn jobserver(pipe: [OwnedFd; 2], child_targets: [libc::c_int; 2]) -> io::Result<Self> {
        if child_targets[0] < 3 || child_targets[1] < 3 || child_targets[0] == child_targets[1] {
            return Err(refused("invalid scoped GNU target descriptor pair"));
        }
        Self::new(Vec::from(pipe), child_targets, Role::Jobserver)
    }

    /// Serve original named FIFO witnesses without converting MAKEFLAGS to a
    /// numeric pipe or requiring any advertised descriptor slot to be closed.
    /// The recipient must freshly open its locator against these witnesses.
    pub fn named_fifo(pipe: [OwnedFd; 2]) -> io::Result<Self> {
        validate_named_pair(&pipe)?;
        Self::new(Vec::from(pipe), [2, 0], Role::NamedFifo)
    }

    /// Serve an already-held implicit CPU lease and its original fences.
    /// Recipients must independently validate actual pool/fence membership.
    pub fn cpu_bundle(primary: OwnedFd, fences: Vec<OwnedFd>) -> io::Result<Self> {
        if fences.len() >= MAX_CPU_FILES {
            return Err(refused("scoped CPU bundle exceeds its descriptor bound"));
        }
        validate_cpu_file(&primary)?;
        for fence in &fences {
            validate_fence_file(fence)?;
        }
        let mut files = vec![primary];
        files.extend(fences);
        let count = files.len() as libc::c_int;
        Self::new(files, [count, 0], Role::CpuBundle)
    }

    fn new(files: Vec<OwnedFd>, pair: [libc::c_int; 2], role: Role) -> io::Result<Self> {
        let scope = Arc::new(Mutex::new(Scope::Unbound));
        Ok(Self(Arc::new(Endpoint::new_scoped_resources(
            Arc::new(files),
            pair,
            &std::env::temp_dir(),
            role,
            Some(scope),
        )?)))
    }

    /// Consume the single bind attempt. Failure leaves the endpoint inert.
    /// The kernel identity includes PID, birth and parent; no caller-supplied
    /// numerical birth or environment string authorizes a member.
    pub fn bind_child(&self, pid: u32) -> io::Result<()> {
        let scope = self.0.scope.as_ref().ok_or_else(|| refused("missing member scope"))?;
        let mut scope = scope.lock().map_err(|_| refused("poisoned member scope"))?;
        if !matches!(*scope, Scope::Unbound) {
            return Err(refused("scoped handoff bind attempt already consumed"));
        }
        *scope = Scope::Failed;
        *scope = Scope::Bound(Process::direct_child(pid)?);
        Ok(())
    }

    /// Publish before spawn; the endpoint refuses every request until binding.
    pub fn advertisement(&self) -> &OsStr {
        &self.0.advertisement
    }

    /// Configure the correct CPU/GNU advertisement, retaining this endpoint.
    /// GNU callers separately configure MAKEFLAGS with their child targets.
    pub fn configure(&self, command: &mut std::process::Command) {
        self.0.configure(command);
    }
}

pub(super) fn authorize(
    scope: Option<&Mutex<Scope>>,
    requester: &Process,
) -> io::Result<Vec<Process>> {
    let Some(scope) = scope else { return Ok(Vec::new()) };
    let member = match &*scope.lock().map_err(|_| refused("poisoned member scope"))? {
        Scope::Bound(member) => member.clone(),
        _ => return Err(refused("scoped handoff is not armed")),
    };
    let member = member.refresh_registered_member()?;
    if member.pid() == requester.pid() {
        if member.birth() != requester.birth() {
            return Err(refused("scoped handoff member PID was replaced"));
        }
        requester.ensure_unchanged()?;
        return Ok(vec![member, requester.clone()]);
    }
    ancestry(&member, requester)
}

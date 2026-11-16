// Trust: one adapter for frontend, LLVM and linker credit ownership.
use std::io;

#[cfg(any(target_os = "linux", target_os = "macos"))]
use trust_build_cpu::{Credit, WorkerClient, WorkerHelper};

#[derive(Clone)]
pub struct Client {
    local: jobserver_crate::Client,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) global: Option<WorkerClient>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) handoff: Option<std::sync::Arc<jobserver_utils::CpuLeaseHandoff>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    native_v3: Option<std::sync::Arc<super::runtime_v3::NativeV3>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    bootstrap_fixed: Option<std::sync::Arc<super::bootstrap_fixed::BootstrapFixed>>,
}

#[derive(Debug)]
pub enum Acquired {
    Local(jobserver_crate::Acquired),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Global(Credit),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    BootstrapFixed(jobserver_utils::quiescence::Acquired),
}

pub enum HelperThread {
    Local(jobserver_crate::HelperThread),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Global(WorkerHelper),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    BootstrapFixed(jobserver_utils::quiescence::HelperThread),
}

impl Client {
    /// Trust: lend the waiting caller's one execution to a child compiler.
    /// This transfers only the same GNU transport, never a fresh pool or native
    /// worker grant. The caller must serialize loans and retain the returned
    /// owner through the entire child wait. Native workers require their own
    /// admitted child profile and refuse this ordinary transport-only route.
    pub(super) fn for_compiler_descendant(&self) -> Result<jobserver_utils::Jobserver, String> {
        if self.is_global() {
            return Err(
                "a native worker child compiler requires an admitted execution profile".into()
            );
        }
        super::early::for_compiler_descendant(&self.local)
    }

    pub fn is_global(&self) -> bool {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.global.is_some()
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            false
        }
    }
    pub(super) fn from_local(local: jobserver_crate::Client) -> Self {
        Self {
            local,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            global: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            handoff: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            native_v3: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            bootstrap_fixed: None,
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn with_global(local: jobserver_crate::Client, global: WorkerClient) -> Self {
        Self {
            local,
            global: Some(global),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            handoff: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            native_v3: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            bootstrap_fixed: None,
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn with_native_v3(
        local: jobserver_crate::Client,
        global: WorkerClient,
        custody: std::sync::Arc<super::runtime_v3::NativeV3>,
    ) -> Self {
        let mut client = Self::with_global(local, global);
        client.native_v3 = Some(custody);
        client
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn with_bootstrap_fixed(
        local: jobserver_crate::Client,
        custody: std::sync::Arc<super::bootstrap_fixed::BootstrapFixed>,
    ) -> Self {
        let mut client = Self::from_local(local);
        client.bootstrap_fixed = Some(custody);
        client
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn bootstrap_fixed_context(
        &self,
    ) -> Option<std::sync::Arc<super::bootstrap_fixed::BootstrapFixed>> {
        self.bootstrap_fixed.clone()
    }
    pub fn is_native_v3(&self) -> bool {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.native_v3.is_some()
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            false
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn native_context(&self) -> Option<std::sync::Arc<super::runtime_v3::NativeV3>> {
        self.native_v3.clone()
    }

    #[cfg(test)]
    pub(super) fn new(limit: usize) -> io::Result<Self> {
        jobserver_crate::Client::new(limit).map(Self::from_local)
    }

    #[cfg(test)]
    pub(super) fn acquire(&self) -> io::Result<Acquired> {
        self.local.acquire().map(Acquired::Local)
    }

    #[cfg(test)]
    pub(super) fn available(&self) -> io::Result<usize> {
        self.local.available()
    }

    pub fn try_acquire(&self) -> io::Result<Option<Acquired>> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(fixed) = &self.bootstrap_fixed {
            return fixed.extras().try_acquire().map(|credit| credit.map(Acquired::BootstrapFixed));
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(global) = &self.global {
            return global.try_acquire().map(|credit| credit.map(Acquired::Global));
        }
        self.local.try_acquire().map(|credit| credit.map(Acquired::Local))
    }

    pub fn into_helper_thread(
        self,
        mut callback: impl FnMut(io::Result<Acquired>) + Send + 'static,
    ) -> io::Result<HelperThread> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(fixed) = self.bootstrap_fixed {
            return fixed
                .extras()
                .clone()
                .into_helper_thread(move |credit| {
                    callback(credit.map(Acquired::BootstrapFixed));
                })
                .map(HelperThread::BootstrapFixed);
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(global) = self.global {
            return global
                .into_helper_thread(move |credit| {
                    callback(credit.map(Acquired::Global));
                })
                .map(HelperThread::Global);
        }
        self.local
            .into_helper_thread(move |credit| callback(credit.map(Acquired::Local)))
            .map(HelperThread::Local)
    }
}

impl Acquired {
    /// Cancel an unused offer before it can enter an SDK task. Native workload
    /// loans are returned explicitly, with GNU custody retained through ACK.
    pub fn retire_unused(self) -> io::Result<()> {
        match self {
            Self::Local(_) => Ok(()),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(_) => Ok(()),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(credit) => credit.retire_unused(),
        }
    }

    /// # Safety
    /// The exact producing SDK task using this credit must have been joined or
    /// positively parked, with no producing children or work left using it.
    pub unsafe fn retire_after_sdk_quiescence(self) -> io::Result<()> {
        match self {
            Self::Local(_) => Ok(()),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(_) => Ok(()),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(credit) => {
                // SAFETY: the caller establishes this exact SDK task's quiescence.
                unsafe { credit.retire_after_sdk_quiescence() }
            }
        }
    }

    /// Commit only at a runnable worker's dispatch edge, never on queue arrival.
    pub fn commit(&mut self) -> bool {
        match self {
            Self::Local(_) => true,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(credit) => credit.commit(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(credit) => credit.commit(),
        }
    }

    /// Global credits must be freshly admitted again between completed tasks,
    /// so a live pressure decrease can drain the active population.
    pub fn was_committed(&self) -> bool {
        match self {
            Self::Local(_) => false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(_) => false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(credit) => credit.is_committed(),
        }
    }
}

impl HelperThread {
    pub fn request_token(&self) {
        match self {
            Self::Local(helper) => helper.request_token(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(helper) => {
                helper.request_token().expect("private Fixed admission is paused or poisoned")
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(helper) => helper.request_token(),
        }
    }

    /// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): withdraw one request whose token
    /// has not been fetched; true if one was withdrawn. A caller that satisfied
    /// its waiter some other way uses this so the helper does not take a token
    /// nobody waits for. The pipe helper cannot be stopped once it is reading
    /// the pool for a request; the global helper polls, and retires a credit
    /// it fetched for a withdrawn request without calling the callback.
    pub fn cancel_request(&self) -> bool {
        match self {
            Self::Local(helper) => helper.cancel_request(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(helper) => {
                helper.cancel_request().expect("private Fixed helper cancellation is poisoned")
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(helper) => helper.cancel_request(),
        }
    }

    /// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): the requests that
    /// `cancel_request` could still withdraw.
    #[cfg(test)]
    pub(super) fn queued_requests(&self) -> usize {
        match self {
            Self::Local(helper) => helper.queued_requests(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(helper) => helper.queued_requests(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(helper) => helper.outstanding_requests(),
        }
    }

    /// Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): retire the helper thread, with no
    /// bound on the wait. The pipe helper's `Drop` gives up after about a
    /// second, and a helper that outlives it can hold a token it has read and
    /// not yet delivered, which process exit then destroys. The global
    /// helper's `Drop` already joins without a bound but hides how the thread
    /// ended. `Ok` means the thread was joined and its callback did not
    /// panic. `Err` means the callback panicked or the thread could not be
    /// told to stop; in the second case it may still be running.
    pub fn shutdown_blocking(self) -> io::Result<()> {
        match self {
            Self::Local(helper) => helper.shutdown_blocking(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::BootstrapFixed(helper) => helper.shutdown_blocking(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Global(helper) => helper.shutdown(),
        }
    }
}

//! Trust (D2, 2026-09-28): the certified-monitor seal decision of one
//! compiler-tool process, as a value that can only be CAPTURED.
//!
//! The seal (`seal_certified_monitor_graph_compiler_environment` in the parent
//! module) deletes every `DYLD_*`/`LD_*` name, while the verified exec edge
//! (`validate_verified_command_runtime_library_authority`, which runs AFTER the
//! seal) requires the platform search variable to begin with the authenticated
//! startup closure. Before D2 the two contradicted each other and every unit of
//! an evidence-grade `targo trust test` failed with "missing its authenticated
//! `DYLD_FALLBACK_LIBRARY_PATH` runtime-library closure". The seal therefore
//! reinstalls exactly one loader value, and that value must travel from the
//! capture to every place the seal is applied.
//!
//! It used to travel as a bare `Option<OsString>` beside a bare `bool`, so a
//! call site passing `None` (or `false`) reintroduced D2 while every
//! non-ignored test still passed (review of `cb/targo-trust-test`, measured).
//! A [`CertifiedMonitorSeal`] carries both, its fields are private to this
//! module, and the only production constructor is [`CertifiedMonitorSeal::capture`]:
//! no call site can pair an enforced seal with a missing or hand-written loader
//! value, and the exec-edge predicate is read here rather than passed in.

use std::ffi::{OsStr, OsString};
use std::path::Path;

use crate::GlobalContext;
use crate::util::CargoResult;

pub(super) const MEMORY_SOCKET_ENV: &str = "TRUST_MEMORY_JOBSERVER_SOCK";

/// One process's certified-monitor seal: its enforcement decision, loader
/// closure and authenticated frontend's memory-admission endpoint.
#[derive(Clone, Debug)]
pub(super) struct CertifiedMonitorSeal {
    enforced: bool,
    authenticated_loader_search: Option<OsString>,
    authenticated_memory_socket: Option<OsString>,
}

impl CertifiedMonitorSeal {
    /// Capture the seal for a process whose lane decided
    /// `execution_tcb_enforced`, judged against the authenticated compiler
    /// image (`Compilation::authenticated_compiler_program`).
    ///
    /// The loader value is `Some` exactly when the seal is enforced AND the
    /// verified exec-edge validator will run (the same
    /// `is_targo_invocation() && trust_verified_targo()` predicate, read here
    /// so no caller can pass a different one). It is
    /// `configure_verified_tool_loader_environment`'s value: the authenticated
    /// compiler's startup closure plus `/usr/lib` on macOS, computed from the
    /// frozen closure and never read back from a command (`get_env` would fall
    /// through to Targo's own environment when the command has no entry).
    pub(super) fn capture(
        execution_tcb_enforced: bool,
        authenticated_compiler: &Path,
        gctx: &GlobalContext,
    ) -> CargoResult<Self> {
        Self::capture_with_exec_edge(
            execution_tcb_enforced,
            super::verified_targo_protocol_active(),
            authenticated_compiler,
            gctx.get_env_os(MEMORY_SOCKET_ENV),
        )
    }

    /// Tests drive both exec-edge states; production code cannot choose one.
    #[cfg(test)]
    pub(super) fn capture_for_test(
        execution_tcb_enforced: bool,
        verified_exec_edge: bool,
        authenticated_compiler: &Path,
    ) -> CargoResult<Self> {
        Self::capture_with_exec_edge(
            execution_tcb_enforced,
            verified_exec_edge,
            authenticated_compiler,
            Some(OsStr::new("/trusted/test-memory.sock")),
        )
    }

    #[cfg(test)]
    pub(super) fn capture_for_test_with_memory(
        execution_tcb_enforced: bool,
        verified_exec_edge: bool,
        authenticated_compiler: &Path,
        socket: Option<&OsStr>,
    ) -> CargoResult<Self> {
        Self::capture_with_exec_edge(
            execution_tcb_enforced,
            verified_exec_edge,
            authenticated_compiler,
            socket,
        )
    }

    fn capture_with_exec_edge(
        execution_tcb_enforced: bool,
        verified_exec_edge: bool,
        authenticated_compiler: &Path,
        memory_socket: Option<&OsStr>,
    ) -> CargoResult<Self> {
        // The authenticated frontend selects and validates this endpoint.
        // Capture it before any package-controlled command overlays, just as
        // we capture the compiler's loader closure. A missing endpoint cannot
        // become an uncoordinated compiler or solver invocation.
        let authenticated_memory_socket =
            if execution_tcb_enforced && verified_exec_edge {
                let socket = memory_socket.ok_or_else(|| anyhow::anyhow!(
                "certified test compilation requires the frontend's memory-admission endpoint"
            ))?;
                if !Path::new(socket).is_absolute() {
                    anyhow::bail!("certified test memory-admission endpoint must be absolute");
                }
                Some(socket.to_owned())
            } else {
                None
            };
        let authenticated_loader_search = if !(execution_tcb_enforced && verified_exec_edge)
            || !cfg!(unix)
        {
            // Off the monitor lane the seal is a no-op; off the verified
            // lane the exec-edge validator is. Non-Unix hosts are refused
            // by the seal itself.
            None
        } else {
            if !authenticated_compiler.is_absolute() {
                anyhow::bail!(
                    "verified Targo selected non-absolute compiler path `{}` while deriving the certified-monitor loader search value",
                    authenticated_compiler.display()
                );
            }
            crate::util::process_authority::verified_tool_loader_search_value(
                authenticated_compiler,
            )?
        };
        Ok(Self {
            enforced: execution_tcb_enforced,
            authenticated_loader_search,
            authenticated_memory_socket,
        })
    }

    /// Whether the seal applies at all (the lane claims proof authority and a
    /// certified-monitor session is active).
    pub(super) fn is_enforced(&self) -> bool {
        self.enforced
    }

    /// The one loader search value the seal reinstalls, if any.
    pub(super) fn authenticated_loader_search(&self) -> Option<&OsStr> {
        self.authenticated_loader_search.as_deref()
    }

    pub(super) fn authenticated_memory_socket(&self) -> Option<&OsStr> {
        self.authenticated_memory_socket.as_deref()
    }
}

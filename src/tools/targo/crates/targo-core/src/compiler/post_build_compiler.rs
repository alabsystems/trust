//! Retain the build's actual scheduler selection for post-build compiler work.
//! Doctests compile after the unit queue joins. They must not lose its GNU
//! owner, mint a replacement pool, or clear native-entry custody requirements.

use anyhow::Context as _;
use cargo_util::{Jobserver, ProcessBuilder};

use crate::util::CargoResult;

pub(super) enum Scheduler {
    Ordinary(Jobserver),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Fixed,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Native(std::sync::Arc<super::resource_runtime::ResourceRuntime>),
}

impl Scheduler {
    pub(super) fn prepare(
        &self,
        mut command: ProcessBuilder,
        #[cfg(any(target_os = "linux", target_os = "macos"))] fixed: Option<
            super::resource_gnu_fixed::FixedTargetJobserver,
        >,
    ) -> CargoResult<Execution> {
        match self {
            Self::Ordinary(selected) => {
                let owner = selected
                    .for_descendant()
                    .context("failed to retain post-build compiler scheduler")?;
                command.inherit_jobserver(&owner);
                Ok(Execution(Prepared::Ordinary {
                    command,
                    _owner: owner,
                }))
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Fixed => {
                anyhow::ensure!(
                    fixed.is_some(),
                    "post-build compiler lost its fixed GNU owner"
                );
                Ok(Execution(Prepared::Fixed(
                    super::target_execution::TargetExecution::new(command, fixed)?,
                )))
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Native(runtime) => {
                let owner = runtime
                    .try_root(true)?
                    .context("post-build compiler has no admitted original native root")?;
                owner.configure(&mut command, true)?;
                Ok(Execution(Prepared::Native {
                    command,
                    _owner: owner,
                }))
            }
        }
    }
}

pub(crate) struct Execution(Prepared);

enum Prepared {
    Ordinary {
        command: ProcessBuilder,
        _owner: Jobserver,
    },
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Fixed(super::target_execution::TargetExecution),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Native {
        command: ProcessBuilder,
        _owner: std::sync::Arc<super::resource_runtime::RootContext>,
    },
}

impl Execution {
    pub(crate) fn exec(self) -> CargoResult<()> {
        match self.0 {
            Prepared::Ordinary { command, _owner } => command.exec(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Prepared::Fixed(execution) => execution.exec(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Prepared::Native { command, _owner } => command.exec(),
        }
    }
}

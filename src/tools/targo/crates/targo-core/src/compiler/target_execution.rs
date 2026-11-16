//! Post-compilation direct targets retain the same actual fixed/GNU owners.
//! Managed test-action queues keep their own scheduler and never use this path.

use crate::util::CargoResult;
use cargo_util::ProcessBuilder;

pub(crate) struct TargetExecution {
    command: ProcessBuilder,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fixed: Option<super::resource_gnu_fixed::FixedTargetJobserver>,
}

impl TargetExecution {
    pub(super) fn new(
        command: ProcessBuilder,
        #[cfg(any(target_os = "linux", target_os = "macos"))] fixed: Option<
            super::resource_gnu_fixed::FixedTargetJobserver,
        >,
    ) -> CargoResult<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let mut command = command;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(owner) = &fixed {
            let selected = owner.jobserver().for_descendant()?;
            command.inherit_jobserver(&selected);
        }
        Ok(Self {
            command,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            fixed,
        })
    }

    pub(crate) fn command(&mut self) -> &mut ProcessBuilder {
        &mut self.command
    }

    /// Direct targets return their observed result only after explicit GNU
    /// settlement; missing bytes retain original custody and remain failure.
    pub(crate) fn exec(self) -> CargoResult<()> {
        let Self {
            command,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            mut fixed,
        } = self;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(owner) = &mut fixed {
            return command.exec_in_original_group_with_retirement(|| owner.retire());
        }
        command.exec()
    }

    /// A run target needs a live supervisor while a broker/scheduler exists.
    /// The original outer group still owns cancellation/descendant retirement.
    pub(crate) fn exec_replace(self, broker: bool) -> CargoResult<()> {
        let Self {
            command,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            mut fixed,
        } = self;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if broker || command.has_jobserver() {
            return command.exec_replace_supervised_with_retirement(|| {
                if let Some(owner) = &mut fixed {
                    owner.retire()?;
                }
                Ok(())
            });
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        assert!(
            !broker,
            "nested-unverified root brokers run only on Linux and macOS"
        );
        command.exec_replace()
    }
}

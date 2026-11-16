//! Distinct full60 service entry. Actual authenticated paired startup precedes
//! project/lane configuration; workload-v1 never routes through this handler.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod control;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod session;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;

pub const PROTOCOL_MARKER: [u8; 64] =
    trust_resource_controller::paired_qualification::PAIRED_PROTOCOL_MARKER;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) fn harness_node(
    target: &str,
    action: trust_test_execution::workload::Action,
) -> crate::util::CargoResult<trust_resource_controller::paired_qualification::service::Node> {
    use anyhow::Context as _;
    use trust_resource_controller::paired_qualification::service::Node;
    let target = trust_test_execution::workload::TARGETS
        .iter()
        .position(|name| *name == target)
        .context("native action outside original paired target population")?
        as u32;
    Ok(match action {
        trust_test_execution::workload::Action::Inventory => Node::Inventory { target },
        trust_test_execution::workload::Action::Sample { repetition } => {
            // Existing native libtest actions are numbered 1..=R. The new
            // paired service's closed node population is indexed 0..R.
            let repetition = repetition
                .checked_sub(1)
                .filter(|index| *index < trust_test_execution::workload::MAX_REPETITIONS)
                .context("native sample outside original paired population")?;
            Node::Sample { target, repetition }
        }
    })
}

pub fn requested(args: &[std::ffi::OsString]) -> bool {
    args.first().is_some_and(|argument| {
        argument == trust_resource_controller::paired_qualification::PAIRED_STARTUP_ARGUMENT
    })
}
pub fn run(
    args: &[std::ffi::OsString],
    bootstrap: crate::workload_service::Bootstrap,
    configure_lane: impl FnOnce() -> crate::util::CargoResult<()>,
) -> crate::util::CargoResult<()> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        supported::run(args, bootstrap, configure_lane)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = (args, bootstrap, configure_lane);
        anyhow::bail!("native paired qualification is unsupported on this platform")
    }
}

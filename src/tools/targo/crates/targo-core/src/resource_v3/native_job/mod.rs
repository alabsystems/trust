//! Genuine general native job Root. Its distinct authenticated startup retains
//! the original all-domain bank; a plan/header/digest cannot create this owner.
pub(crate) mod startup;
pub(crate) mod outputs;
use std::sync::Arc;
use crate::util::CargoResult;
pub(crate) fn require(plan: &Arc<trust_resource_controller::native_job::Plan>) -> CargoResult<Arc<super::Startup>> {
    let startup=super::current().ok_or_else(|| anyhow::anyhow!("native job has no original startup"))?;
    anyhow::ensure!(startup.original_root && startup.paired_invocation.is_none()
        && startup.native_job_plan.as_ref().is_some_and(|held| Arc::ptr_eq(held,plan))
        && startup.workload_bank.is_some() && startup.workload_control.is_some()
        && startup.workload_process.is_some() && startup.descriptor_budget.is_some(),
        "native job replaced its actual Root/plan/bank/original inputs");
    let process=startup.workload_process.as_ref().ok_or_else(||anyhow::anyhow!("native job lost original process lifetime"))?;
    anyhow::ensure!(std::time::Instant::now()<process.deadline
        && !process.cancelled.load(std::sync::atomic::Ordering::Acquire)
        && !process.poisoned.load(std::sync::atomic::Ordering::Acquire),
        "native job original Root lifetime is cancelled, poisoned or expired");
    trust_resource_controller::client::sdk::validate_sdk_keeper(&startup._context)?;
    let actual=trust_resource_provenance::process::read_identity(std::process::id())?;
    anyhow::ensure!(startup._context.original_root.pid==actual.pid && startup._context.original_root.birth==actual.birth,
        "native job is not its original Root process");
    Ok(startup)
}

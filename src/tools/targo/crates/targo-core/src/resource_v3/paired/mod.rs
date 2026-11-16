//! A decoded new plan cannot opt an old root into verification. Actual new
//! startup alone installs paired_invocation after48/49v2 plus original SCM
//! adoption. Planning here still grants no member execution or proof authority.
use super::*;
use anyhow::ensure;
use std::os::unix::ffi::OsStrExt as _;
use trust_resource_controller::paired_qualification::PairedInvocation;

pub(crate) fn require(plan: &PairedInvocation) -> CargoResult<Arc<Startup>> {
    plan.validate()?;
    let original = current().context("paired graph has no authenticated native root")?;
    ensure!(
        original.original_root && original.paired_invocation.as_deref() == Some(plan),
        "paired graph requires distinct authenticated48/49v2; workload-v1 cannot expand"
    );
    let bank = original
        .workload_bank
        .as_ref()
        .context("paired graph lost original CPU bank")?;
    let evidence = original
        .workload_evidence
        .as_ref()
        .context("paired graph lost original evidence writer")?;
    let process = original
        .workload_process
        .as_ref()
        .context("paired graph lost original process/SDK inputs")?;
    let mut hash = cargo_util::Sha256::new();
    hash.update(&plan.binding_preimage()?);
    let digest = hash.finish();
    ensure!(
        bank.binds(original.query.binding.root_attempt, digest)
            && evidence.root_attempt() == original.query.binding.root_attempt
            && evidence.invocation_sha256() == digest
            && crate::ops::cargo_test::workload::evidence::is_installed(evidence)
            && !evidence.failed(),
        "paired graph lost its complete60 original bank/evidence binding"
    );
    ensure!(
        std::time::Instant::now() < process.deadline
            && !process.cancelled.load(std::sync::atomic::Ordering::Acquire)
            && !process.poisoned.load(std::sync::atomic::Ordering::Acquire),
        "paired original root is expired, stopped or poisoned"
    );
    ensure!(
        process.compiler.root().as_os_str().as_bytes() == plan.consumer.root
            && process.compiler.program().as_os_str().as_bytes() == plan.consumer.compiler.path
            && process.compiler.observation().executable.sha256
                == hex::encode(plan.consumer.compiler.sha256),
        "paired graph cannot substitute its original held SDK compiler"
    );
    process.sysroot.validate(
        process
            .deadline
            .min(std::time::Instant::now() + std::time::Duration::from_secs(20)),
    )?;
    Ok(original)
}

pub(crate) mod startup;

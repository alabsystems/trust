//! Normal full consumer compilation and its native actions share one graph.
//! Only authenticated original startup can call this entry; all saved service
//! data stays diagnostic and never grants custody/admission or source proof.
use super::{Bootstrap, session::Session, transport::Input};
use crate::{
    compiler::{Compilation, UserIntent},
    ops,
    util::{CargoResult, Filesystem, GlobalContext},
    workspace::Workspace,
};
use anyhow::Context as _;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};
use trust_resource_controller::{
    CompletionCause, Status,
    workload::{WorkloadInvocation, budget, host::census, service::finish},
};

fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}

pub(super) fn run(
    args: &[OsString],
    bootstrap: Bootstrap,
    configure_lane: impl FnOnce() -> CargoResult<()>,
) -> CargoResult<()> {
    anyhow::ensure!(
        args.len() == 1 && super::requested(args),
        "native workload entry accepts only its exact private argument"
    );
    let entered = bootstrap.entered;
    let mut input = Input::capture_stdin()?;
    let until = entered
        .checked_add(Duration::from_nanos(budget::STARTUP_NS))
        .context("native startup deadline unrepresentable")?;
    let invocation = WorkloadInvocation::decode(&input.frame(until, None)?)?;
    let mode = super::startup_mode(args).context("original startup mode disappeared")?;
    let prepared =
        crate::resource_v3::workload::startup::prepare(invocation, bootstrap, entered, mode)?;
    let (session, root_control) = Session::new(prepared, input)?;
    session.ready()?;
    session.begin_compile(session.startup.local_ceiling)?;
    // The existing exact explicit-unverified lane starts its process-local
    // broker once. It mutates no global environment; project/configuration and
    // every compiler query still follow original startup/mandatory executor.
    configure_lane()?;
    let mut gctx = GlobalContext::new(
        session.shell(),
        path(&session.invocation.cwd),
        path(&session.invocation.cargo_home),
    );
    gctx.install_root_control(root_control)?;
    let compiled = compile(&session, &mut gctx);
    let mut failure = compiled.as_ref().err().map(|error| format!("{error:#}"));
    if !session.has_compiler_checkpoint() {
        if let Err(error) = session.failed_before_compiler_checkpoint(
            failure
                .clone()
                .unwrap_or_else(|| "normal compiler graph omitted its required checkpoint".into()),
        ) {
            failure.get_or_insert_with(|| format!("{error:#}"));
        }
    }
    let semantic_success = match &compiled {
        Ok(compilation) => compilation.test_execution.as_ref().is_some_and(|run| {
            run.completed.len() == 2 + 2 * session.invocation.repetitions as usize
                && run.blocked.is_empty()
                && run.interruption.is_none()
                && run.reporting_error.is_none()
                && run.workload_outputs.is_some()
                && run.completed.iter().all(|completion| {
                    completion.result.is_ok()
                        && completion
                            .workload
                            .as_ref()
                            .is_some_and(|action| action.native_terminal())
                })
        }),
        Err(_) => false,
    };
    if !semantic_success {
        failure.get_or_insert(
            "native graph did not complete its entire original harness population successfully"
                .into(),
        );
    }
    if let Err(error) = session.inputs.validate() {
        failure.get_or_insert_with(|| format!("original inputs changed: {error:#}"));
    }
    if let Err(error) = session.finish_input() {
        failure.get_or_insert_with(|| format!("original input control failed: {error:#}"));
    }
    if session
        .startup
        .workload_process
        .as_ref()
        .is_some_and(|process| process.cancelled.load(std::sync::atomic::Ordering::Acquire))
    {
        failure
            .get_or_insert("original workload stop intent prevents a complete comparison".into());
    }
    let settlement = Instant::now()
        .checked_add(Duration::from_nanos(budget::SETTLEMENT_NS))
        .context("native settlement deadline unrepresentable")?
        .min(session.deadline);
    let bank = session
        .startup
        .workload_bank
        .as_ref()
        .context("graph lost original bank")?;
    bank.park()?;
    while !bank.is_drained()? {
        anyhow::ensure!(
            Instant::now() < settlement,
            "original graph bank did not positively drain"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
    let mut broker = session
        .startup
        .workload_control
        .as_ref()
        .context("graph lost original control")?
        .lock()
        .map_err(|_| anyhow::anyhow!("original graph control poisoned"))?
        .take()
        .context("original graph control already consumed")?;
    broker.drained()?;
    let mut control = broker.finish()?;
    let nonce = crate::resource_v3::call_attempt(session.binding.root_attempt)?;
    let mut snapshot = control.census_snapshot(nonce, settlement)?;
    let mut entries = Vec::new();
    loop {
        match snapshot.next_page(settlement) {
            Ok(Some(page)) => {
                entries.try_reserve(page.len())?;
                entries.extend(page);
            }
            Ok(None) => break,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                anyhow::ensure!(
                    Instant::now() < settlement,
                    "original host census did not become quiescent"
                );
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(error) => return Err(error.into()),
        }
    }
    anyhow::ensure!(
        snapshot.complete() && snapshot.total() == Some(entries.len() as u32),
        "original host census is incomplete"
    );
    if let Ok(compilation) = &compiled {
        if let Some(run) = &compilation.test_execution {
            let mut observed = std::collections::BTreeSet::new();
            for completion in &run.completed {
                let (capture, member) = match retained_action(completion.workload.as_ref()) {
                    Ok(actual) => actual,
                    Err(error) => {
                        failure.get_or_insert_with(|| format!("{error:#}"));
                        continue;
                    }
                };
                let kind = match completion.action.workload_action {
                    Some(trust_test_execution::workload::Action::Inventory) => {
                        census::SourceKind::Inventory
                    }
                    Some(trust_test_execution::workload::Action::Sample { .. }) => {
                        census::SourceKind::Sample
                    }
                    None => {
                        failure.get_or_insert(
                            "native completion omitted its original workload action".into(),
                        );
                        continue;
                    }
                };
                let matching = entries
                    .iter()
                    .filter(|entry| entry.member_attempt == member && entry.kind == kind)
                    .collect::<Vec<_>>();
                if !observed.insert(member) || matching.len() != 1 {
                    failure.get_or_insert("native action is missing, repeated or misbound in the complete original target census".into());
                    continue;
                }
                if let Err(error) = compare_action(capture, matching[0]) {
                    failure.get_or_insert_with(|| format!("{error:#}"));
                }
            }
        }
    }
    if entries.iter().any(|entry| {
        !entry.retired
            || !entry.drained
            || entry.accounting.cpu_times.is_none()
            || entry.accounting.peak_rss_bytes.is_none()
            || !matches!(
                entry.terminal,
                Status::Finished {
                    cause: CompletionCause::Exited,
                    ..
                }
            )
    }) {
        failure.get_or_insert("complete native action census has uncertain retirement or unavailable owning-wait measurements".into());
    }
    if let Err(error) = session.inputs.validate() {
        failure.get_or_insert_with(|| format!("final original inputs changed: {error:#}"));
    }
    if let Some(sink) = &session.startup.workload_evidence {
        if let Err(error) = sink.synchronize(settlement) {
            failure.get_or_insert_with(|| {
                format!("original failed-output sink incomplete: {error:#}")
            });
        }
        if sink.failed() {
            failure.get_or_insert("original output/evidence sink is incomplete".into());
        }
    }
    // Repage only these same complete observations. Neither data pages nor
    // Graph replace original Root/cohort retirement, exit or outer stream EOF.
    if entries.is_empty() {
        session.send(&finish::encode_page(&census::Page {
            request: census::Request {
                root_attempt: session.binding.root_attempt,
                invocation_sha256: session.binding.invocation_sha256,
                snapshot: nonce,
                offset: 0,
            },
            total: 0,
            entries: Vec::new(),
        })?)?;
    }
    let mut offset = 0;
    while offset < entries.len() {
        let mut count = (entries.len() - offset).min(census::MAX_PAGE_ENTRIES);
        let bytes = loop {
            let page = census::Page {
                request: census::Request {
                    root_attempt: session.binding.root_attempt,
                    invocation_sha256: session.binding.invocation_sha256,
                    snapshot: nonce,
                    offset: offset as u32,
                },
                total: entries.len() as u32,
                entries: entries[offset..offset + count].to_vec(),
            };
            match finish::encode_page(&page) {
                Ok(bytes) => break bytes,
                Err(_) if count > 1 => count /= 2,
                Err(error) => return Err(error.into()),
            }
        };
        session.send(&bytes)?;
        offset += count;
    }
    session.send(
        &finish::Graph {
            binding: session.binding.clone(),
            succeeded: failure.is_none(),
            snapshot: nonce,
            members: entries.len() as u32,
        }
        .encode()?,
    )?;
    // Keep actual finalized outputs/guards through final reporting and native
    // command Drained. Host still holds original descriptions until real exit.
    drop(compiled);
    if let Some(failure) = failure {
        anyhow::bail!("{failure}");
    }
    Ok(())
}

fn compile<'a>(
    session: &Arc<Session>,
    gctx: &'a mut GlobalContext,
) -> CargoResult<Compilation<'a>> {
    let target = path(&session.invocation.output_root);
    gctx.configure(
        0,
        false,
        Some("never"),
        false,
        true,
        true,
        &Some(target.clone()),
        &[],
        &[],
    )?;
    let mut workspace = Workspace::new(&path(&session.invocation.cwd).join("Cargo.toml"), gctx)?;
    workspace.set_target_dir(Filesystem::new(target));
    session
        .inputs
        .validate_target(workspace.target_dir().as_path_unlocked())?;
    let mut options = ops::CompileOptions::new(gctx, UserIntent::Test)?;
    options.build_config.jobs = options.build_config.jobs.min(session.startup.local_ceiling);
    session.record_jobs(options.build_config.jobs)?;
    options.spec = ops::Packages::Packages(vec!["trust-vc-core".into()]);
    options.filter = ops::CompileFilter::from_raw_arguments(
        false,
        Vec::new(),
        false,
        trust_test_execution::workload::TARGETS
            .iter()
            .map(|target| (*target).to_owned())
            .collect(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    );
    let plan = crate::ops::cargo_test::workload::Plan::new(
        session.invocation.repetitions,
        Duration::from_nanos(session.invocation.timeout_ns),
    )?;
    let graph = crate::ops::cargo_test::workload::Options {
        plan,
        observer: session.clone(),
        inputs: session.inputs.clone(),
    }
    .graph(&workspace)?;
    let compilation = ops::cargo_compile::compile_with_test_execution(&workspace, &options, graph)?;
    anyhow::ensure!(
        !session
            .startup
            .workload_process
            .as_ref()
            .context("lost original process inputs")?
            .poisoned
            .load(std::sync::atomic::Ordering::Acquire),
        "an original compiler query failed; graph cannot substitute cached success"
    );
    Ok(compilation)
}

/// Consistency only: neither capture nor census data constructs a live member.
/// The caller retains the original graph and requires its native retirement.
fn retained_action(
    action: Option<&crate::ops::cargo_test::workload::CapturedAction>,
) -> CargoResult<(&crate::ops::cargo_test::workload::CapturedAction, [u8; 16])> {
    let action = action.context("native completion omitted its actual workload capture")?;
    anyhow::ensure!(
        action.native_terminal(),
        "native completion omitted its original complete native terminal"
    );
    let member = action
        .capture
        .owner_observation
        .and_then(|owner| owner.native_member_attempt)
        .context("native completion omitted its original member binding")?;
    Ok((action, member))
}

fn compare_action(
    action: &crate::ops::cargo_test::workload::CapturedAction,
    entry: &census::Entry,
) -> CargoResult<()> {
    use std::os::unix::process::ExitStatusExt as _;
    anyhow::ensure!(
        action.native_terminal(),
        "native action lacks its actual complete owner terminal"
    );
    let owner = action
        .capture
        .owner_observation
        .context("native action has no original owner observation")?;
    anyhow::ensure!(
        owner.native_member_attempt == Some(entry.member_attempt)
            && entry.started.is_some()
            && entry.retired
            && entry.drained,
        "native action differs from its original member identity/retirement"
    );
    let Status::Finished {
        outcome,
        cause,
        runtime_ns,
    } = entry.terminal
    else {
        anyhow::bail!("native action census has no original finished terminal");
    };
    let status = action
        .capture
        .status
        .context("native action has no actual exit observation")?;
    let actual = status
        .code()
        .map(trust_resource_controller::Outcome::Exit)
        .or_else(|| {
            status
                .signal()
                .map(trust_resource_controller::Outcome::Signal)
        });
    anyhow::ensure!(
        actual == Some(outcome),
        "native action exit outcome differs from its original target census"
    );
    let expected = match cause {
        CompletionCause::Exited => cargo_util::CaptureCompletionCause::Exited,
        CompletionCause::Timeout => cargo_util::CaptureCompletionCause::Timeout,
        CompletionCause::Cancelled => cargo_util::CaptureCompletionCause::Cancelled,
        CompletionCause::ResourceLimit => cargo_util::CaptureCompletionCause::ResourceLimit,
        CompletionCause::HostFault => cargo_util::CaptureCompletionCause::HostFault,
    };
    anyhow::ensure!(
        owner.target_runtime == Some(Duration::from_nanos(runtime_ns))
            && owner.cause == Some(expected),
        "native action runtime/cause differs from its original target census"
    );
    anyhow::ensure!(
        entry.accounting.peak_rss_bytes == action.stats.peak_rss
            && entry.accounting.cpu_times.map(|cpu| (
                Duration::from_nanos(cpu.user_ns),
                Duration::from_nanos(cpu.system_ns)
            )) == action.stats.cpu_times.map(|cpu| (cpu.user, cpu.system)),
        "native action accounting differs from its original target census"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt as _;
    use trust_resource_controller::{
        BirthKind, Identity, Outcome, Started,
        accounting::{Observation, Scope},
    };

    // Saved-data projections exercise only the final consistency predicate;
    // they create no output, member, retirement or execution eligibility.
    #[test]
    fn workload_action_census_rejects_different_outcome_and_missing_original_facts() {
        let identity = Identity {
            pid: 123,
            birth: 456,
            birth_kind: BirthKind::MacosWallMicroseconds,
        };
        let mut action = crate::ops::cargo_test::workload::CapturedAction {
            capture: cargo_util::CapturedProcess {
                started: true,
                status: Some(std::process::ExitStatus::from_raw(0)),
                stdout_end: cargo_util::CaptureStreamEnd::Eof,
                stderr_end: cargo_util::CaptureStreamEnd::Eof,
                owner_observation: Some(cargo_util::CaptureOwnerObservation {
                    native_member_attempt: Some([1; 16]),
                    target_runtime: Some(Duration::from_nanos(10)),
                    cause: Some(cargo_util::CaptureCompletionCause::Exited),
                    retirement_confirmed: true,
                }),
                ..Default::default()
            },
            stats: cargo_util::ExecStats::default(),
        };
        let mut entry = census::Entry {
            member_attempt: [1; 16],
            kind: census::SourceKind::Inventory,
            identity: Some(identity),
            started: Some(Started {
                identity,
                monotonic_ns: 1,
                unix_ns: 2,
            }),
            terminal: Status::Finished {
                outcome: Outcome::Exit(0),
                cause: CompletionCause::Exited,
                runtime_ns: 10,
            },
            accounting: Observation {
                scope: Scope::ChildAndWaitedDescendantsV1,
                cpu_times: None,
                peak_rss_bytes: None,
            },
            retired: true,
            drained: true,
        };
        assert!(compare_action(&action, &entry).is_ok());
        entry.terminal = Status::Finished {
            outcome: Outcome::Exit(7),
            cause: CompletionCause::Exited,
            runtime_ns: 10,
        };
        assert!(
            compare_action(&action, &entry)
                .unwrap_err()
                .to_string()
                .contains("outcome")
        );
        entry.terminal = Status::Finished {
            outcome: Outcome::Exit(0),
            cause: CompletionCause::Exited,
            runtime_ns: 11,
        };
        assert!(
            compare_action(&action, &entry)
                .unwrap_err()
                .to_string()
                .contains("runtime")
        );
        entry.terminal = Status::Finished {
            outcome: Outcome::Exit(0),
            cause: CompletionCause::Exited,
            runtime_ns: 10,
        };
        entry.member_attempt = [2; 16];
        assert!(compare_action(&action, &entry).is_err());
        entry.member_attempt = [1; 16];
        entry.started = None;
        assert!(compare_action(&action, &entry).is_err());
        assert!(retained_action(None).is_err());
        assert_eq!(retained_action(Some(&action)).unwrap().1, [1; 16]);
        action.capture.owner_observation = None;
        assert!(retained_action(Some(&action)).is_err());
    }
}

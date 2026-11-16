//! The real paired native stages, under one original root and runtime. Source
//! qualification and performance/proof comparison remain independent consumers.
use super::session::{AyObserver, ConsumerObserver, Session, reason};
use crate::context::root_control::RootControl;
use crate::ops::paired_qualification;
use crate::util::{CargoResult, GlobalContext};
use crate::workload_service::{Bootstrap, transport::Input};
use anyhow::Context as _;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use trust_resource_controller::paired_qualification::{
    PairedInvocation,
    service::{self, Node},
};
use trust_resource_controller::workload::{budget, host::census};

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
        "paired entry accepts only its exact private argument"
    );
    let entered = Instant::now();
    let mut input = Input::capture_stdin()?;
    let invocation = PairedInvocation::decode(
        &input.frame(entered + Duration::from_nanos(budget::STARTUP_NS), None)?,
    )?;
    let prepared = crate::resource_v3::paired::startup::prepare(invocation, bootstrap, entered)?;
    let (session, root_control) = Session::new(prepared, input)?;
    session.ready()?;
    session.register(Node::AyCompile, None)?;
    session.begin_phase()?;
    let attempted = (|| {
        configure_lane()?;
        graphs(&session, root_control)
    })();
    let mut failures = Vec::new();
    let mut retained = match attempted {
        Ok(graph) => {
            failures.extend(graph.failures.iter().cloned());
            Some(graph)
        }
        Err(cause) => {
            failures.push(reason(cause));
            None
        }
    };
    // Both scoped graph calls have returned, including their actual joins;
    // close any writer/timer left by preparation failure before reporting.
    for node in [Node::AyCompile, Node::ConsumerCompile] {
        if let Err(cause) = session.close_remaining_stage(node) {
            failures.push(reason(cause));
        }
    }
    // Every required node remains in the denominator, including preparation
    // failures. A broken transport may prevent publication, never shrink it.
    for node in Node::population(session.plan.consumer.repetitions)? {
        if !session.has_finished(node)?
            && let Err(cause) = session.blocked(
                node,
                "original prerequisite, input, admission or observation failed",
            )
        {
            failures.push(reason(cause));
        }
    }
    let rebound = session.inputs.validate();
    if let Err(cause) = &rebound {
        failures.push(reason(cause));
    }
    if let Err(cause) = session.finish_input() {
        failures.push(reason(cause));
    }
    if session
        .startup
        .workload_process
        .as_ref()
        .is_some_and(|process| process.cancelled.load(Ordering::Acquire))
    {
        failures.push("original paired input or observation stopped the graph".into());
    }
    let until =
        (Instant::now() + Duration::from_nanos(budget::SETTLEMENT_NS)).min(session.deadline);
    let bank = session
        .startup
        .workload_bank
        .as_ref()
        .context("paired graph lost original bank")?;
    bank.park()?;
    while !bank.is_drained()? {
        anyhow::ensure!(
            Instant::now() < until,
            "paired original bank did not positively drain"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
    let mut broker = session
        .startup
        .workload_control
        .as_ref()
        .context("paired graph lost original control")?
        .lock()
        .map_err(|_| anyhow::anyhow!("paired original control poisoned"))?
        .take()
        .context("paired original control consumed twice")?;
    broker.drained()?;
    let mut control = broker.finish()?;
    let nonce = crate::resource_v3::call_attempt(session.binding.root_attempt)?;
    let mut snapshot = control.census_snapshot(nonce, until)?;
    let mut entries = Vec::new();
    loop {
        match snapshot.next_page(until) {
            Ok(Some(page)) => {
                entries.try_reserve(page.len())?;
                entries.extend(page);
            }
            Ok(None) => break,
            Err(cause) if cause.kind() == std::io::ErrorKind::WouldBlock => {
                anyhow::ensure!(
                    Instant::now() < until,
                    "paired actual host census did not become quiescent"
                );
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(cause) => return Err(cause.into()),
        }
    }
    anyhow::ensure!(
        snapshot.complete() && snapshot.total() == Some(entries.len() as u32),
        "paired full native census incomplete"
    );
    if let Err(cause) = session.validate_census(&entries) {
        failures.push(reason(cause));
    }
    let final_inputs = session.inputs.validate();
    if let Err(cause) = &final_inputs {
        failures.push(reason(cause));
    }
    // Abort synchronization seals this SAME sink only after every actual graph
    // worker, callback and input reader has joined. Never use it at a normal
    // between-stage checkpoint; those synchronize just their original action.
    let sink = session
        .startup
        .workload_evidence
        .as_ref()
        .context("paired graph lost actual sink")?;
    if let Err(cause) = sink.synchronize(until) {
        failures.push(reason(cause));
    }
    if sink.failed() {
        failures.push("paired original raw evidence is incomplete".into());
    }
    if entries.is_empty() {
        session.send(&service::encode_census(&census::Page {
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
            match service::encode_census(&page) {
                Ok(bytes) => break bytes,
                Err(_) if count > 1 => count /= 2,
                Err(cause) => return Err(cause.into()),
            }
        };
        session.send(&bytes)?;
        offset += count;
    }
    let (finished, blocked) = session.counts()?;
    session.send(
        &service::Final {
            binding: session.binding.clone(),
            repetitions: session.plan.consumer.repetitions,
            finished,
            blocked,
            inputs_unchanged: rebound.is_ok() && final_inputs.is_ok(),
            snapshot: nonce,
            members: entries.len() as u32,
        }
        .encode()?,
    )?;
    // Keep original command/input/output capsules through complete reporting
    // and actual native Drained. Host retains SAME descriptions past Root exit.
    drop(retained.take());
    if failures.is_empty() {
        Ok(())
    } else {
        anyhow::bail!("{}", failures.join("; "))
    }
}
struct Graphs {
    failures: Vec<String>,
    _ay: crate::compiler::qualification::Run,
    _consumer: Option<crate::ops::cargo_test::graph::TestGraphRun>,
    _control: RootControl,
}
fn graphs(session: &Arc<Session>, root: RootControl) -> CargoResult<Graphs> {
    let ay = paired_qualification::run_ay(
        session.plan.clone(),
        session.inputs.clone(),
        Arc::new(AyObserver(session.clone())),
        session.shell(Node::AyCompile),
        root,
    )?;
    let mut failures = Vec::new();
    if let Err(cause) = &ay.result {
        failures.push(reason(cause));
    }
    if !session.has_finished(Node::AyCompile)? {
        session.compile_finished(
            Node::AyCompile,
            false,
            Some("AY preparation failed before complete compiler graph".into()),
        )?;
    }
    for (action, cause) in &ay.verification.blocked {
        let node = if action.index.0 == 0 {
            Node::Advisory
        } else {
            Node::Strict
        };
        session.blocked(node, cause)?;
    }
    if ay.verification.completed.len() != 2
        || !ay.verification.blocked.is_empty()
        || ay.verification.reporting_failure.is_some()
        || ay
            .verification
            .completed
            .iter()
            .any(|completion| !completion.complete_observation())
    {
        failures
            .push("AY verification did not complete both original independent observations".into());
    }
    if ay
        .verification
        .completed
        .iter()
        .find(|completion| completion.action.index.0 == 0)
        .is_none_or(|completion| !completion.capture.passed())
    {
        failures.push("original advisory verification did not exit successfully".into());
    }
    session.close_stage(Node::AyCompile)?;
    let stopped = ay.continuation_failure.is_some()
        || ay.input_failure.is_some()
        || session
            .startup
            .workload_process
            .as_ref()
            .is_some_and(|process| {
                process.poisoned.load(Ordering::Acquire)
                    || process.cancelled.load(Ordering::Acquire)
            });
    if stopped {
        failures.push(
            ay.continuation_failure
                .clone()
                .or(ay.input_failure.clone())
                .unwrap_or_else(|| "original paired continuation was stopped".into()),
        );
        session.close_stage(Node::ConsumerCompile)?;
        return Ok(Graphs {
            failures,
            _ay: ay.verification,
            _consumer: None,
            _control: ay.control,
        });
    }
    session.register(Node::ConsumerCompile, None)?;
    session.begin_phase()?;
    let mut context = GlobalContext::new(
        session.shell(Node::ConsumerCompile),
        path(&session.plan.consumer.cwd),
        path(&session.plan.consumer.cargo_home),
    );
    context.install_root_control(ay.control)?;
    let consumer = paired_qualification::run_consumer(
        &mut context,
        &session.plan,
        session.inputs.clone(),
        Arc::new(ConsumerObserver(session.clone())),
        ay.continuation,
    );
    let run = match consumer {
        Ok(mut compilation) => {
            let run = compilation.test_execution.take();
            drop(compilation);
            run
        }
        Err(cause) => {
            failures.push(reason(cause));
            None
        }
    };
    if !session.has_finished(Node::ConsumerCompile)? {
        session.compile_finished(
            Node::ConsumerCompile,
            false,
            Some("consumer preparation failed before complete compiler graph".into()),
        )?;
    }
    if run.as_ref().is_none_or(|run| {
        run.completed.len() != 2 + 2 * session.plan.consumer.repetitions as usize
            || !run.blocked.is_empty()
            || run.interruption.is_some()
            || run.reporting_error.is_some()
            || run.workload_outputs.is_none()
            || run.completed.iter().any(|completion| {
                completion.result.is_err()
                    || completion
                        .workload
                        .as_ref()
                        .is_none_or(|actual| !actual.native_terminal())
            })
    }) {
        failures.push(
            "consumer did not complete its entire original native target/test population".into(),
        );
    }
    let root = context
        .into_root_control()
        .context("consumer lost the original cancellation endpoint")?;
    session.close_stage(Node::ConsumerCompile)?;
    Ok(Graphs {
        failures,
        _ay: ay.verification,
        _consumer: run,
        _control: root,
    })
}

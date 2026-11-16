//! Keep the original compiler queue and scheduling owners across qualification.
//! A compile checkpoint is not execution authority. Only the private one-use
//! grant plus the current complete authority manifest can release test nodes.

use std::sync::Arc;
use std::time::{Duration, Instant};

use cargo_util::StreamingProcessScope;
use trust_test_execution::retained::RetainedChild;
use trust_test_execution::{PreparedTests, PreparedTestsReceipt};

use super::auth_scheduling::OwnedSchedulingHandoff;
use super::graph::{TestAction, TestGraphOptions};
use super::*;

pub(crate) struct Gate {
    child: RetainedChild,
    deadline: Instant,
    checkpointed: bool,
    authorized: Option<Arc<Authorized>>,
}

impl Gate {
    pub(crate) fn take(gctx: &GlobalContext) -> CargoResult<Self> {
        anyhow::ensure!(
            crate::is_targo_invocation() && crate::trust_verified_targo(),
            "retained queue requires authenticated verified Targo"
        );
        let child = gctx.take_retained_test().ok_or_else(|| {
            anyhow::anyhow!("retained queue has no original private session endpoint")
        })?;
        let deadline = child.deadline();
        Ok(Self {
            child,
            // The original frontend absolute deadline survives qualification.
            deadline,
            checkpointed: false,
            authorized: None,
        })
    }

    pub(crate) fn retain_through_command_result(self, gctx: &GlobalContext) -> CargoResult<()> {
        gctx.retain_completed_test_endpoint(self.child)?;
        Ok(())
    }

    pub(crate) fn authorized(&self) -> Option<Arc<Authorized>> {
        self.authorized.clone()
    }

    pub(crate) fn publish_failed(
        &mut self,
        message: &str,
        gctx: &GlobalContext,
    ) -> CargoResult<()> {
        if self.checkpointed {
            return Ok(());
        }
        flush_compiler_output(gctx)?;
        self.child.publish_compile_failed(message, self.deadline)?;
        self.checkpointed = true;
        Ok(())
    }

    pub(crate) fn qualify(
        &mut self,
        ws: &Workspace<'_>,
        options: &TestGraphOptions,
        compilation: &Compilation<'_>,
        actions: &[&TestAction],
        signals: &StreamingProcessScope,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            !self.checkpointed,
            "retained compilation checkpoint is one-use"
        );
        let (plan, receipt) =
            prepared::export_retained(ws, options, compilation, self.child.session())?;
        validate_queue_plan(&plan, actions)?;
        flush_compiler_output(ws.gctx())?;
        self.child.publish_ready(&receipt, self.deadline)?;
        self.checkpointed = true;
        let grant = loop {
            anyhow::ensure!(
                !prepared::cancelled(ws.gctx(), signals),
                "retained verification was cancelled before execution authority"
            );
            if let Some(grant) = self.child.poll_grant(self.deadline)? {
                break grant;
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        let authority = load_test_execution_authority_from_inputs(
            grant.session(),
            grant.authority_path(),
            grant.authority_sha256(),
        )?;
        let authorized = Authorized::bind(authority, plan, &receipt, grant.plan_sha256())?;
        // Validate cancellation again after all path/hash checks. A grant can
        // never make a previously observed stop reversible.
        anyhow::ensure!(
            !self.child.poll_cancelled()? && !prepared::cancelled(ws.gctx(), signals),
            "retained verification was cancelled before dispatch"
        );
        self.authorized = Some(Arc::new(authorized));
        Ok(())
    }

    pub(crate) fn poll_cancelled(&mut self) -> CargoResult<bool> {
        Ok(self.child.poll_parent_closed()?)
    }
}

fn flush_compiler_output(gctx: &GlobalContext) -> CargoResult<()> {
    use std::io::Write as _;
    let mut shell = gctx.shell();
    shell.out().flush()?;
    shell.err().flush()?;
    std::io::stdout().flush()?;
    std::io::stderr().flush()?;
    Ok(())
}

fn validate_queue_plan(plan: &PreparedTests, actions: &[&TestAction]) -> CargoResult<()> {
    anyhow::ensure!(
        plan.tests.len() == actions.len(),
        "retained plan changed the queued test population"
    );
    for (index, (test, action)) in plan.tests.iter().zip(actions).enumerate() {
        anyhow::ensure!(
            action.index == index
                && action.total == actions.len()
                && action.path.canonicalize()? == Path::new(&test.executable)
                && action.unit.target.name() == test.target,
            "retained plan does not name the original queued test action {index}"
        );
    }
    Ok(())
}

/// Immutable exact plan plus the existing fully checked manifest. It contains
/// no queue Units or ambient environment and can be shared with owned workers.
pub(crate) struct Authorized {
    authority: TestExecutionAuthority,
    plan: PreparedTests,
}

impl Authorized {
    fn bind(
        authority: TestExecutionAuthority,
        plan: PreparedTests,
        receipt: &PreparedTestsReceipt,
        grant_plan_sha256: &str,
    ) -> CargoResult<Self> {
        anyhow::ensure!(
            receipt.session == plan.session,
            "retained receipt differs from the plan session"
        );
        let bytes = serde_json::to_vec(&plan)?;
        anyhow::ensure!(
            receipt.sha256 == grant_plan_sha256
                && Sha256::new().update(&bytes).finish_hex() == receipt.sha256,
            "retained grant differs from the original prepared plan"
        );
        let accepted = authority.prepared.as_ref().ok_or_else(|| {
            anyhow::anyhow!("retained authority is missing the exact prepared test plan")
        })?;
        anyhow::ensure!(
            serde_json::to_vec(accepted)? == bytes,
            "current execution authority changed the retained command plan"
        );
        for test in &plan.tests {
            anyhow::ensure!(
                test.env.get("RUST_TEST_THREADS").map(String::as_str) == Some("1"),
                "retained harness exceeds its one queued worker credit"
            );
        }
        Ok(Self { authority, plan })
    }

    pub(crate) fn command(&self, index: usize) -> CargoResult<(String, ProcessBuilder)> {
        let test = self.plan.tests.get(index).ok_or_else(|| {
            anyhow::anyhow!("retained test index is outside the authenticated population")
        })?;
        let path = Path::new(&test.executable);
        self.authority.validate_executable(path)?;
        let mut command = ProcessBuilder::new(path);
        command
            .args(&test.args)
            .cwd(&test.cwd)
            .environment_snapshot(cargo_util::EnvironmentInputs::from_variables(
                test.env
                    .iter()
                    .map(|(key, value)| (OsString::from(key), OsString::from(value))),
            )?);
        strip_test_execution_authority_env(&mut command);
        Ok((test.target.clone(), command))
    }

    pub(crate) fn execute(
        &self,
        index: usize,
        command: &ProcessBuilder,
        signals: &StreamingProcessScope,
        scheduling: &OwnedSchedulingHandoff,
    ) -> CargoResult<()> {
        let test = self.plan.tests.get(index).ok_or_else(|| {
            anyhow::anyhow!("retained execution index is outside the authenticated population")
        })?;
        let path = Path::new(&test.executable);
        self.authority.validate_executable(path)?;
        let result = execute_authenticated_test_with_cancel_and_scheduling(
            &self.authority,
            path,
            command,
            &mut || signals.interrupted(),
            Some(scheduling),
        );
        // Preserve the existing post-execution substitution refusal too; it
        // runs before the exit record is written, so a refused harness never
        // has its exit recorded as an exit.
        let validated = self.authority.validate_executable(path);
        // Trust: how the harness ended, beside its per-case result file.
        let recorded = prepared::record_harness_end(&self.plan.session, test, &result, &validated);
        validated?;
        result.and(recorded)
    }
}

#[cfg(all(test, any(target_arch = "x86_64", target_arch = "aarch64")))]
mod tests {
    use super::*;

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "authenticated marker child reads its actual post-exec environment before a Cargo context exists"
    )]
    fn retained_authenticated_marker_fixture() {
        if let Some(marker) = env::var_os("TARGO_RETAINED_MARKER") {
            fs::write(marker, b"executed-authenticated-retained-plan").unwrap();
        }
    }

    fn fixture(root: &Path) -> (TestExecutionAuthority, PreparedTests, PreparedTestsReceipt) {
        let executable = root.join("retained-test-image");
        fs::copy(env::current_exe().unwrap(), &executable).unwrap();
        let executable = executable.canonicalize().unwrap();
        let (sha256, size) = exact_regular_test_executable_identity(&executable).unwrap();
        let test = trust_test_execution::PreparedTest {
            target: "retained-marker".into(),
            executable: executable.to_str().unwrap().into(),
            sha256: sha256.clone(),
            size,
            cwd: root.to_str().unwrap().into(),
            args: vec![
                "--exact".into(),
                "ops::cargo_test::retained::tests::retained_authenticated_marker_fixture".into(),
                "--test-threads=1".into(),
            ],
            env: [
                ("RUST_TEST_THREADS".into(), "1".into()),
                ("NUM_JOBS".into(), "1".into()),
                ("CARGO_BUILD_JOBS".into(), "1".into()),
                ("TARGO_PLANNED_JOBS".into(), "1".into()),
                (
                    "TARGO_RETAINED_MARKER".into(),
                    root.join("marker").to_str().unwrap().into(),
                ),
            ]
            .into_iter()
            .collect(),
            results: None,
        };
        let plan = PreparedTests {
            schema: trust_test_execution::PLAN_SCHEMA.into(),
            session: "retained-native-regression".into(),
            host_os: env::consts::OS.into(),
            host_arch: env::consts::ARCH.into(),
            target_directory: root.to_str().unwrap().into(),
            no_fail_fast: false,
            tests: vec![test],
        };
        let receipt = PreparedTestsReceipt {
            schema: trust_test_execution::RECEIPT_SCHEMA.into(),
            session: plan.session.clone(),
            path: root.join("prepared.json").to_str().unwrap().into(),
            sha256: Sha256::new()
                .update(&serde_json::to_vec(&plan).unwrap())
                .finish_hex(),
        };
        let authority = TestExecutionAuthority {
            executables: [(
                executable.clone(),
                TestExecutionAuthorityEntry {
                    target: "retained-marker".into(),
                    path: executable.to_str().unwrap().into(),
                    sha256,
                    size,
                },
            )]
            .into_iter()
            .collect(),
            prepared: Some(plan.clone()),
        };
        (authority, plan, receipt)
    }

    fn execute(authorized: &Authorized) -> CargoResult<()> {
        let (_, command) = authorized.command(0)?;
        let scope = StreamingProcessScope::new()?;
        let jobserver = cargo_util::Jobserver::new(1)?;
        let scheduling = OwnedSchedulingHandoff::jobserver_only(&jobserver)?;
        let result = authorized.execute(0, &command, &scope, &scheduling);
        scope.finish()?;
        result
    }

    #[test]
    fn exact_retained_plan_executes_the_authenticated_image() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path().canonicalize().unwrap();
        let (authority, plan, receipt) = fixture(&root);
        let authorized = Authorized::bind(authority, plan, &receipt, &receipt.sha256).unwrap();
        execute(&authorized).unwrap();
        assert_eq!(
            fs::read(root.join("marker")).unwrap(),
            b"executed-authenticated-retained-plan"
        );
    }

    #[test]
    fn changed_grant_or_current_manifest_cannot_dispatch_retained_command() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path().canonicalize().unwrap();
        let (authority, plan, receipt) = fixture(&root);
        let error = Authorized::bind(authority, plan, &receipt, &"0".repeat(64))
            .err()
            .expect("foreign grant must fail");
        assert!(error.to_string().contains("original prepared plan"));
        assert!(!root.join("marker").exists());

        let (mut authority, plan, receipt) = fixture(&root);
        authority.prepared.as_mut().unwrap().tests[0]
            .env
            .insert("RUST_TEST_THREADS".into(), "2".into());
        let result = Authorized::bind(authority, plan, &receipt, &receipt.sha256)
            .and_then(|accepted| execute(&accepted));
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("changed the retained command plan")
        );
        assert!(!root.join("marker").exists());
    }

    #[test]
    fn retained_artifact_substitution_and_prior_cancellation_never_run_marker() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path().canonicalize().unwrap();
        let (authority, plan, receipt) = fixture(&root);
        let authorized = Authorized::bind(authority, plan, &receipt, &receipt.sha256).unwrap();
        let (_, command) = authorized.command(0).unwrap();
        let scope = StreamingProcessScope::new().unwrap();
        scope.cancel();
        let jobserver = cargo_util::Jobserver::new(1).unwrap();
        let scheduling = OwnedSchedulingHandoff::jobserver_only(&jobserver).unwrap();
        assert!(
            authorized
                .execute(0, &command, &scope, &scheduling)
                .is_err()
        );
        assert!(!root.join("marker").exists());
        let _ = scope.finish();
        fs::write(
            &authorized.plan.tests[0].executable,
            b"substituted artifact",
        )
        .unwrap();
        assert!(execute(&authorized).is_err());
        assert!(!root.join("marker").exists());
    }
}

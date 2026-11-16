//! The ordinary queue uses one shared actual-GNU ready waiter. Its owner
//! creates no pool/CPU/SDK and joins the physical helper before returning any
//! fetched credit; no Full-specific scheduling policy lives in this layer.
pub(super) use jobserver_utils::ready::ReadyTokenAdmission;

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests {
    use super::*;
    use cargo_util::{ProcessBuilder, StreamingOutputLimits, StreamingProcessScope};
    use jobserver::Client;
    use std::path::{Path, PathBuf};
    use std::time::{Duration, Instant};

    const COORDINATOR: &str =
        "compiler::job_queue::ready_token::tests::inherited_two_credit_coordinator_fixture";
    const HARNESS: &str = "compiler::job_queue::ready_token::tests::rendezvous_harness_fixture";

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "child rendezvous actor reads its parent's actual environment before a Cargo context exists"
    )]
    fn rendezvous_harness_fixture() {
        let Some(root) = std::env::var_os("TARGO_READY_TOKEN_HARNESS_ROOT") else {
            return;
        };
        let root = PathBuf::from(root);
        let own = std::env::var("TARGO_READY_TOKEN_HARNESS_INDEX").unwrap();
        let peer = if own == "first" { "second" } else { "first" };
        std::fs::write(root.join(&own), b"running").unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while !root.join(peer).exists() {
            assert!(
                Instant::now() < deadline,
                "two-credit test was silently serialized"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
        // Neither real harness can return before both entered user code.
        std::fs::write(root.join(format!("{own}-completed")), b"both-running").unwrap();
    }

    fn harness(root: &Path, index: &str, scope: &StreamingProcessScope) -> crate::CargoResult<()> {
        let mut command = ProcessBuilder::new(std::env::current_exe()?);
        command
            .arg("--exact")
            .arg(HARNESS)
            .arg("--test-threads=1")
            .env("TARGO_READY_TOKEN_HARNESS_ROOT", root)
            .env("TARGO_READY_TOKEN_HARNESS_INDEX", index)
            .supervised_by(scope);
        command.exec_with_streaming_limits(
            &mut |_| Ok(()),
            &mut |_| Ok(()),
            false,
            StreamingOutputLimits::new(1024 * 1024, 16 * 1024 * 1024).with_child_exit_cleanup(),
        )?;
        Ok(())
    }

    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "child coordinator reads its parent's actual environment before a Cargo context exists"
    )]
    fn inherited_two_credit_coordinator_fixture() {
        let Some(root) = std::env::var_os("TARGO_READY_TOKEN_COORDINATOR_ROOT") else {
            return;
        };
        let root = PathBuf::from(root);
        // SAFETY: our parent supplied and retains these exact live pipe ends
        // through this real child; no ambient or reused descriptor is adopted.
        let imported = unsafe { Client::from_env_ext(true) }.client.unwrap();
        #[cfg(target_os = "macos")]
        assert_eq!(
            imported.try_acquire().unwrap_err().kind(),
            std::io::ErrorKind::Unsupported,
            "this regression must exercise the inherited GNU pipe fallback"
        );
        let scope = StreamingProcessScope::new().unwrap();
        let mut admission = ReadyTokenAdmission::default();
        std::thread::scope(|threads| {
            let mut cancel = super::super::test_action::CancelTestWorkers::new(Some(&scope));
            let first = threads.spawn(|| harness(&root, "first", &scope));
            let deadline = Instant::now() + Duration::from_secs(5);
            while !root.join("first").exists() {
                assert!(
                    Instant::now() < deadline,
                    "implicit-credit harness did not start"
                );
                std::thread::sleep(Duration::from_millis(5));
            }
            assert!(!root.join("first-completed").exists());
            let credit = loop {
                if let Some(credit) = admission.try_acquire(&imported).unwrap() {
                    break credit;
                }
                assert!(
                    Instant::now() < deadline,
                    "original GNU pool's second credit was lost"
                );
                std::thread::sleep(Duration::from_millis(5));
            };
            let second = threads.spawn(|| {
                let _credit = credit;
                harness(&root, "second", &scope)
            });
            first.join().unwrap().unwrap();
            second.join().unwrap().unwrap();
            cancel.disarm();
        });
        admission.retire();
        scope.finish().unwrap();
        assert!(root.join("first-completed").exists());
        assert!(root.join("second-completed").exists());
    }

    #[test]
    fn inherited_gnu_two_credit_harnesses_overlap_without_a_new_pool() {
        let root = tempfile::tempdir().unwrap();
        let original = Client::new(2).unwrap();
        // This actual original credit is lent implicitly to the coordinator.
        // Its only supplementary credit must be returned to this same pipe.
        let implicit = original.acquire().unwrap();
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command
            .arg("--exact")
            .arg(COORDINATOR)
            .arg("--test-threads=1")
            .env("TARGO_READY_TOKEN_COORDINATOR_ROOT", root.path());
        original.configure(&mut command);
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "coordinator failed: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(root.path().join("first-completed").exists());
        assert!(root.path().join("second-completed").exists());
        // Both harnesses and the imported coordinator have joined. No other
        // consumer can race this original pipe; inspect its actual population
        // before acquiring (anonymous macOS pipes do not support try_acquire).
        assert_eq!(
            original.available().unwrap(),
            1,
            "original supplementary credit population changed"
        );
        let returned = original.acquire().unwrap();
        assert_eq!(
            original.available().unwrap(),
            0,
            "a second pool minted extra credits"
        );
        drop(returned);
        assert_eq!(original.available().unwrap(), 1);
        drop(implicit);
        assert_eq!(original.available().unwrap(), 2);
    }
}

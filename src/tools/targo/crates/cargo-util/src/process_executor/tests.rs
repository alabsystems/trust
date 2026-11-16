use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};
struct RefusingOwner(AtomicUsize);
impl ProcessExecutor for RefusingOwner {
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "original execution owner refusal",
        ))
    }
    fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "original execution owner refusal",
        ))
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, Result<Output>) {
        self.0.fetch_add(1, Ordering::Relaxed);
        (
            ExecStats::default(),
            Err(anyhow::anyhow!("original execution owner refusal")),
        )
    }
}
#[test]
fn owned_routes_never_retry_locally_or_replace_their_root_on_failure() {
    let owner = Arc::new(RefusingOwner(AtomicUsize::new(0)));
    let mut process = ProcessBuilder::new("/nonexistent-must-not-execute-owned-route");
    process
        .process_executor(owner.clone())
        .retry_with_argfile(true);
    assert!(
        format!("{:#}", process.status().unwrap_err()).contains("original execution owner refusal")
    );
    assert!(
        format!("{:#}", process.output().unwrap_err()).contains("original execution owner refusal")
    );
    let (_, result) = process.exec_with_streaming(&mut |_| Ok(()), &mut |_| Ok(()), true, false);
    assert!(format!("{:#}", result.unwrap_err()).contains("original execution owner refusal"));
    assert!(
        format!("{:#}", process.exec_replace().unwrap_err()).contains("owned hosted execution")
    );
    assert!(
        format!("{:#}", process.exec_replace_supervised().unwrap_err())
            .contains("owned hosted execution")
    );
    assert_eq!(owner.0.load(Ordering::Relaxed), 3);
}

#[test]
fn structured_capture_refuses_unsupported_owner_before_delivery() {
    let owner = Arc::new(RefusingOwner(AtomicUsize::new(0)));
    let mut process = ProcessBuilder::new("/nonexistent-structured-capture-must-not-execute");
    process.process_executor(owner.clone());
    let captured =
        process.exec_with_capture(StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup());
    assert!(!captured.started && captured.status.is_none() && !captured.complete());
    assert!(
        captured
            .failure
            .unwrap()
            .to_string()
            .contains("does not support structured capture")
    );
    assert_eq!(owner.0.load(Ordering::Relaxed), 0);
}

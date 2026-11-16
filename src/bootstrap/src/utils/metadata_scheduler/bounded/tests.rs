use std::time::Duration;

#[test]
fn default_handler_with_auto_reap_still_refuses_wait_ownership() {
    // SAFETY: this local initialized action is inspected only, never installed.
    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
    action.sa_sigaction = libc::SIG_DFL;
    assert!(require_wait_ownership(&action).is_ok());
    action.sa_flags |= libc::SA_NOCLDWAIT;
    assert!(require_wait_ownership(&action).is_err());
    action.sa_flags = 0;
    action.sa_sigaction = libc::SIG_IGN;
    assert!(require_wait_ownership(&action).is_err());
}

use super::*;

#[test]
fn bounded_query_reaps_success_timeout_and_output_refusal() {
    let output =
        run(&mut Command::new("/usr/bin/true"), Instant::now() + Duration::from_secs(2), 1024)
            .unwrap();
    assert!(output.status.success());
    assert!(output.stdout.is_empty() && output.stderr.is_empty());
    let timeout =
        run(Command::new("/bin/sleep").arg("30"), Instant::now() + Duration::from_millis(50), 1024)
            .unwrap_err();
    assert_eq!(timeout.kind(), io::ErrorKind::TimedOut);
    let overflow =
        run(&mut Command::new("/usr/bin/yes"), Instant::now() + Duration::from_secs(2), 1024)
            .unwrap_err();
    assert!(overflow.to_string().contains("output bound"), "{overflow}");
    // A refused query cannot leave the original child or poison the next one.
    assert!(
        run(&mut Command::new("/usr/bin/true"), Instant::now() + Duration::from_secs(2), 1024)
            .unwrap()
            .status
            .success()
    );
}

//! A caught panic must not make an offered CPU unit reusable while its actual
//! hosted target may still execute. Ordinary error paths settle explicitly.
enum State {
    Unoffered,
    PendingDelivery,
    Settled,
}
pub(crate) struct ExecutionLoan(State);
impl ExecutionLoan {
    pub(crate) fn new() -> Self {
        Self(State::Unoffered)
    }
    /// Arm BEFORE calling a delivery API that may offer work and then unwind.
    pub(crate) fn begin_delivery(&mut self) {
        self.0 = State::PendingDelivery;
    }
    /// Call only after affirmative BeforeRequest, Finished, or Refused facts.
    pub(crate) fn settle(&mut self) {
        self.0 = State::Settled;
    }
}
impl Drop for ExecutionLoan {
    fn drop(&mut self) {
        if matches!(self.0, State::PendingDelivery) {
            abort_worker();
        }
    }
}
pub(super) fn abort_worker() -> ! {
    // Workload-only: synchronize actual already-written bounded prefixes with
    // try-locks and one absolute abort deadline. Missing/failed publication
    // remains incomplete; it cannot settle this execution or resume the unit.
    // Ordinary native v3 has no provider and retains its immediate abort path.
    let _ = crate::ops::cargo_test::workload::evidence::synchronize_abort(
        std::time::Instant::now() + std::time::Duration::from_millis(250),
    );
    // SAFETY: terminate only this managed process without false settlement.
    unsafe { libc::_exit(75) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the subprocess mode controls the real exit-75 containment check before a Cargo context exists"
    )]
    fn caught_unwind_cannot_return_an_unresolved_execution_loan() {
        const MODE: &str = "TRUST_EXECUTION_LOAN_TEST";
        let module = module_path!().split_once("::").unwrap().1;
        let exact = format!("{module}::caught_unwind_cannot_return_an_unresolved_execution_loan");
        if let Ok(mode) = std::env::var(MODE) {
            let mut loan = ExecutionLoan::new();
            if mode != "unoffered" {
                loan.begin_delivery();
            }
            if mode == "settled" {
                loan.settle();
            }
            let result = std::panic::catch_unwind(move || {
                let _loan = loan;
                panic!("controlled callback unwind");
            });
            assert!(result.is_err());
            return;
        }
        for (mode, code) in [("unoffered", 0), ("offered", 75), ("settled", 0)] {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &exact])
                .env(MODE, mode)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .unwrap();
            assert_eq!(status.code(), Some(code), "{mode}");
        }
    }
}

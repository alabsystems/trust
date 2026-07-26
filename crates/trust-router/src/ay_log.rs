// trust-router/ay_log.rs: solver-internal tracing diagnostics policy.
//
// Solver internals are not compiler diagnostics. The in-process solver stack
// (ay-dpll, ay-chc via trust-mc, trust-wp, ...) emits `tracing::warn!` events
// mid-solve — e.g. ay-dpll's "asserting theory atom at level 0" — as solver
// developer diagnostics. Inside `trustc` the rustc-installed global tracing
// subscriber enables WARN for ALL targets even without `RUSTC_LOG`
// (`rustc_log::init_logger` falls back to a bare `LevelFilter::WARN`
// directive), so every in-process solve leaked a screenful of
// `WARN ay_dpll::...` lines onto each compile's stderr.
//
// The fix lives on the EMBEDDING side: trust-router scopes tracing's no-op
// subscriber as the THREAD-LOCAL default around each solver invocation
// (`with_ay_diagnostics_policy`), dropping those events — and making the
// solver's own `tracing::enabled!(WARN)` guards false, which skips the
// diagnostic term formatting — without touching the host process's global
// subscriber or any other thread. `TRUST_AY_LOG` opts back in for solver
// debugging.
//
// The scoped-thread-local approach is sound here because the wrapped solves
// run on the calling thread: ay's only internal threads are
// deadline/interrupt watchdogs, which emit no diagnostics. Rayon-parallel
// dispatch is covered because each wrap site executes ON the worker thread
// that runs the solve.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Env knob re-enabling the solvers' internal tracing diagnostics inside the
/// embedding process. Unset (the default), `""`, `"0"`, `"off"`, and
/// `"false"` (case-insensitive) keep them suppressed; any other value (e.g.
/// `TRUST_AY_LOG=warn`) lets solver events flow to the host process's global
/// tracing subscriber again.
pub(crate) const AY_LOG_ENV: &str = "TRUST_AY_LOG";

/// True when the user opted back in to solver tracing diagnostics via
/// [`AY_LOG_ENV`]. Read per solve (uncached) so the knob is testable and a
/// long-lived embedder can toggle it; an env read is noise next to a solve.
fn ay_diagnostics_value_opted_in(value: Option<&str>) -> bool {
    value.is_some_and(|value| {
        !matches!(value.trim().to_ascii_lowercase().as_str(), "" | "0" | "off" | "false")
    })
}

fn ay_diagnostics_opted_in() -> bool {
    ay_diagnostics_value_opted_in(std::env::var(AY_LOG_ENV).ok().as_deref())
}

/// Apply the diagnostics policy for an already-resolved opt-in decision.
///
/// Keeping the process-environment read outside this helper lets tests cover
/// both policy branches without mutating process-global state and racing other
/// in-process solver tests.
pub(crate) fn with_ay_diagnostics_policy_choice<R>(opted_in: bool, f: impl FnOnce() -> R) -> R {
    if opted_in {
        f()
    } else {
        tracing::subscriber::with_default(tracing::subscriber::NoSubscriber::default(), f)
    }
}

/// Run `f` with solver-internal tracing diagnostics suppressed, unless
/// [`AY_LOG_ENV`] opts back in. See the module docs for why and how.
pub(crate) fn with_ay_diagnostics_policy<R>(f: impl FnOnce() -> R) -> R {
    with_ay_diagnostics_policy_choice(ay_diagnostics_opted_in(), f)
}

#[cfg(test)]
mod tests {
    use super::ay_diagnostics_value_opted_in;

    #[test]
    fn diagnostics_opt_in_values_are_classified_without_mutating_the_environment() {
        for disabled in [None, Some(""), Some("  "), Some("0"), Some("OFF"), Some(" false ")] {
            assert!(!ay_diagnostics_value_opted_in(disabled), "unexpected opt-in: {disabled:?}");
        }
        for enabled in [Some("1"), Some("warn"), Some("true"), Some("debug")] {
            assert!(ay_diagnostics_value_opted_in(enabled), "missed opt-in: {enabled:?}");
        }
    }
}

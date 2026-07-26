// trust-router/memory_guard.rs: Process memory monitoring for solver backends
//
// Enforces memory limits on AY/trust-mc backends to prevent OOM
// when multiple agents compile simultaneously. Reads RSS with a single
// `getrusage(RUSAGE_SELF)` syscall on macOS and Linux — NO `ps`/subprocess on
// the hot path (the old per-check `ps` fork was itself a per-dispatch cost and a
// failure mode under memory pressure). The aggregate, cross-process budget lives
// in `memory_jobserver.rs`; this guard is the per-process backstop.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicU64, Ordering};

use thiserror::Error;

/// Errors from the memory guard.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MemoryGuardError {
    /// Process RSS exceeds the configured memory limit.
    #[error("memory limit exceeded: {current_mb}MB used, {limit_mb}MB limit (peak: {peak_mb}MB)")]
    LimitExceeded { current_mb: u64, limit_mb: u64, peak_mb: u64 },

    /// Failed to query process memory from the OS.
    #[error("failed to query process memory: {reason}")]
    QueryFailed { reason: String },
}

/// A snapshot of the process's memory state at a point in time.
#[derive(Debug, Clone, Copy)]
pub struct MemorySnapshot {
    /// Resident set size in bytes.
    pub rss_bytes: u64,
    /// Resident set size in megabytes.
    pub rss_mb: u64,
    /// Configured memory limit in megabytes.
    pub limit_mb: u64,
    /// Current utilization as a percentage (0.0 - 100.0+).
    pub utilization_pct: f64,
}

/// Process memory guard for solver backends.
///
/// Monitors the current process's RSS and enforces a configurable memory
/// limit. Designed to be called before and periodically during solver
/// invocations to prevent OOM kills.
///
/// # Usage
///
/// ```text
/// let guard = MemoryGuard::new(1024); // 1 GB limit
/// match guard.check_memory() {
///     Ok(snapshot) => println!("RSS: {}MB / {}MB", snapshot.rss_mb, snapshot.limit_mb),
///     Err(MemoryGuardError::LimitExceeded { .. }) => return Err(...),
///     Err(e) => eprintln!("memory query failed: {e}"),
/// }
/// ```
pub struct MemoryGuard {
    /// Memory limit in megabytes. 0 = unlimited.
    limit_mb: u64,
    /// Peak RSS observed across all checks (bytes).
    peak_rss_bytes: AtomicU64,
    /// Utilization percentage at which to emit a warning (0.0 - 1.0).
    warning_threshold_pct: f64,
}

impl std::fmt::Debug for MemoryGuard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryGuard")
            .field("limit_mb", &self.limit_mb)
            .field("peak_rss_bytes", &self.peak_rss_bytes.load(Ordering::Relaxed))
            .field("warning_threshold_pct", &self.warning_threshold_pct)
            .finish()
    }
}

impl MemoryGuard {
    /// Create a new memory guard with the given limit in megabytes.
    ///
    /// A limit of 0 disables enforcement (check_memory always succeeds).
    /// Default warning threshold: 75%.
    #[must_use]
    pub fn new(limit_mb: u64) -> Self {
        Self { limit_mb, peak_rss_bytes: AtomicU64::new(0), warning_threshold_pct: 0.75 }
    }

    /// Set the warning threshold as a fraction (0.0 - 1.0).
    ///
    /// At this utilization level, `check_memory` emits a warning to stderr.
    #[must_use]
    pub fn with_warning_threshold(mut self, pct: f64) -> Self {
        self.warning_threshold_pct = pct.clamp(0.0, 1.0);
        self
    }

    /// Query the current process RSS and check it against the limit.
    ///
    /// Returns `Ok(MemorySnapshot)` if within limits, or
    /// `Err(MemoryGuardError::LimitExceeded)` if the RSS exceeds the
    /// configured limit. Emits a warning to stderr at the warning threshold.
    pub fn check_memory(&self) -> Result<MemorySnapshot, MemoryGuardError> {
        let rss_bytes = get_rss_bytes()?;
        let rss_mb = rss_bytes / (1024 * 1024);

        // Update peak RSS.
        let _ = self.peak_rss_bytes.fetch_max(rss_bytes, Ordering::Relaxed);

        let utilization_pct =
            if self.limit_mb > 0 { (rss_mb as f64 / self.limit_mb as f64) * 100.0 } else { 0.0 };

        let snapshot =
            MemorySnapshot { rss_bytes, rss_mb, limit_mb: self.limit_mb, utilization_pct };

        // Check warning threshold (75% default).
        if self.limit_mb > 0 {
            let threshold_mb = (self.limit_mb as f64 * self.warning_threshold_pct) as u64;
            if rss_mb >= threshold_mb && rss_mb < self.limit_mb {
                eprintln!(
                    "Trust memory warning: {rss_mb}MB / {}MB ({utilization_pct:.1}%) \
                     — approaching solver memory limit",
                    self.limit_mb,
                );
            }
        }

        // Check hard limit.
        if self.limit_mb > 0 && rss_mb >= self.limit_mb {
            let peak_bytes = self.peak_rss_bytes.load(Ordering::Relaxed);
            let peak_mb = peak_bytes / (1024 * 1024);
            return Err(MemoryGuardError::LimitExceeded {
                current_mb: rss_mb,
                limit_mb: self.limit_mb,
                peak_mb,
            });
        }

        Ok(snapshot)
    }

    /// Return the peak RSS observed across all `check_memory` calls (bytes).
    #[must_use]
    pub fn peak_rss_bytes(&self) -> u64 {
        self.peak_rss_bytes.load(Ordering::Relaxed)
    }

    /// Return the configured memory limit in megabytes.
    #[must_use]
    pub fn limit_mb(&self) -> u64 {
        self.limit_mb
    }

    /// Return the configured warning threshold as a fraction (0.0 - 1.0).
    #[must_use]
    pub fn warning_threshold_pct(&self) -> f64 {
        self.warning_threshold_pct
    }
}

impl Default for MemoryGuard {
    fn default() -> Self {
        Self::new(default_limit_mb())
    }
}

/// Default per-process RSS ceiling in MB when no explicit
/// `solver_memory_limit_mb` is configured.
///
/// The old hardcoded 1 GB was both too small for a legitimate large solve on a
/// big host and unrelated to the actual machine — the cross-process budget now
/// lives in `memory_jobserver`. Here we derive a per-process ceiling from total
/// RAM (`machine_budget_bytes`), clamped to a sane floor so the guard never trips
/// spuriously on a small solve and never fails open on a huge host. `0` (RAM
/// undetectable) disables the per-process hard limit and defers entirely to the
/// jobserver and the OS — matching the prior "0 = unlimited" semantics.
#[must_use]
fn default_limit_mb() -> u64 {
    let budget = crate::memory_jobserver::machine_budget_bytes();
    if budget == 0 {
        // Total RAM unknown: keep the historical 1 GB backstop rather than
        // disabling the guard entirely.
        return 1024;
    }
    let budget_mb = budget / (1024 * 1024);
    // Floor at 2 GB so a single legitimate solve is never throttled by the
    // per-process guard; the aggregate cap is the jobserver's job.
    budget_mb.max(2048)
}

// ---------------------------------------------------------------------------
// Platform-native RSS queries
// ---------------------------------------------------------------------------

/// Query the current process's resident set size via `getrusage(RUSAGE_SELF)`.
///
/// A SINGLE syscall — no `ps` fork, no `/proc` read, no allocation — so it is
/// cheap enough to call before every dispatch and cannot itself fail under
/// memory pressure the way a subprocess fork can. `ru_maxrss` is the PEAK RSS,
/// which is a conservative (never-under-reporting) proxy for an OOM guard: the
/// glibc/Rust allocators rarely return memory to the OS, so peak tracks current
/// closely for a growing process, and over-reporting only ever trips the guard
/// EARLIER (sound for OOM prevention, never a wrong verdict — the guard returns
/// `Unknown`, never a proof).
///
/// macOS reports `ru_maxrss` in bytes; Linux reports it in kilobytes.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn get_rss_bytes() -> Result<u64, MemoryGuardError> {
    // SAFETY: `libc::rusage` is plain-old-data; zero-init is valid before
    // `getrusage` fills every output field. `usage` points to valid writable
    // memory for the duration of the call.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let ret = unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) };
    if ret != 0 {
        return Err(MemoryGuardError::QueryFailed {
            reason: format!("getrusage failed: {}", std::io::Error::last_os_error()),
        });
    }
    let max_rss = usage.ru_maxrss.max(0) as u64;
    #[cfg(target_os = "macos")]
    {
        Ok(max_rss) // bytes
    }
    #[cfg(target_os = "linux")]
    {
        Ok(max_rss * 1024) // KB -> bytes
    }
}

/// Stub for unsupported platforms.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn get_rss_bytes() -> Result<u64, MemoryGuardError> {
    Err(MemoryGuardError::QueryFailed { reason: "unsupported platform for RSS query".to_string() })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_guard_default_limit() {
        let guard = MemoryGuard::default();
        // The default per-process ceiling is now RAM-derived (>= a 2 GB floor),
        // or the 1 GB historical backstop when total RAM is undetectable — never
        // the old unconditional hardcoded 1 GB on a real host.
        assert!(
            guard.limit_mb() >= 1024,
            "default limit must be at least the 1 GB backstop, got {}",
            guard.limit_mb()
        );
        assert!((guard.warning_threshold_pct() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_limit_mb_is_ram_derived_or_backstop() {
        let mb = super::default_limit_mb();
        // Either the RAM-derived floor (>= 2 GB) or the 1 GB no-RAM backstop.
        assert!(mb == 1024 || mb >= 2048, "unexpected default limit {mb}");
    }

    #[test]
    fn test_memory_guard_custom_limit() {
        let guard = MemoryGuard::new(2048);
        assert_eq!(guard.limit_mb(), 2048);
    }

    #[test]
    fn test_memory_guard_with_warning_threshold() {
        let guard = MemoryGuard::new(1024).with_warning_threshold(0.90);
        assert!((guard.warning_threshold_pct() - 0.90).abs() < f64::EPSILON);
    }

    #[test]
    fn test_memory_guard_warning_threshold_clamped() {
        let guard = MemoryGuard::new(1024).with_warning_threshold(1.5);
        assert!((guard.warning_threshold_pct() - 1.0).abs() < f64::EPSILON);

        let guard2 = MemoryGuard::new(1024).with_warning_threshold(-0.5);
        assert!((guard2.warning_threshold_pct() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_memory_guard_unlimited() {
        let guard = MemoryGuard::new(0);
        assert_eq!(guard.limit_mb(), 0);

        // Should always succeed with unlimited
        let result = guard.check_memory();
        assert!(result.is_ok(), "unlimited guard should not fail: {result:?}");

        let snapshot = result.expect("should get snapshot");
        assert!(snapshot.rss_bytes > 0, "RSS should be nonzero");
        assert!((snapshot.utilization_pct - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_memory_guard_check_returns_snapshot() {
        // Use a very high limit so the check succeeds
        let guard = MemoryGuard::new(64 * 1024); // 64 GB limit
        let result = guard.check_memory();
        assert!(result.is_ok(), "check should succeed with high limit: {result:?}");

        let snapshot = result.expect("should get snapshot");
        assert!(snapshot.rss_bytes > 0, "RSS should be nonzero for a running process");
        assert!(snapshot.rss_mb > 0 || snapshot.rss_bytes > 0, "should have some RSS");
        assert_eq!(snapshot.limit_mb, 64 * 1024);
        assert!(snapshot.utilization_pct >= 0.0);
        assert!(snapshot.utilization_pct < 100.0);
    }

    #[test]
    fn test_memory_guard_peak_tracking() {
        let guard = MemoryGuard::new(64 * 1024);

        // Initial peak should be 0
        assert_eq!(guard.peak_rss_bytes(), 0);

        // After a check, peak should be nonzero
        let _ = guard.check_memory();
        let peak = guard.peak_rss_bytes();
        assert!(peak > 0, "peak RSS should be nonzero after check");

        // After another check, peak should be >= the first
        let _ = guard.check_memory();
        let peak2 = guard.peak_rss_bytes();
        assert!(peak2 >= peak, "peak RSS should not decrease");
    }

    #[test]
    fn test_memory_guard_limit_enforced() {
        // Set limit to 1 MB — the test process definitely uses more than this
        let guard = MemoryGuard::new(1);
        let result = guard.check_memory();
        assert!(result.is_err(), "1MB limit should be exceeded by test process");

        if let Err(MemoryGuardError::LimitExceeded { current_mb, limit_mb, peak_mb }) = result {
            assert_eq!(limit_mb, 1);
            assert!(current_mb >= 1, "current RSS should be at least 1MB");
            assert!(peak_mb >= 1, "peak RSS should be at least 1MB");
        } else {
            panic!("expected LimitExceeded error");
        }
    }

    #[test]
    fn test_memory_snapshot_utilization() {
        let snapshot = MemorySnapshot {
            rss_bytes: 512 * 1024 * 1024, // 512 MB
            rss_mb: 512,
            limit_mb: 1024,
            utilization_pct: 50.0,
        };
        assert!((snapshot.utilization_pct - 50.0).abs() < f64::EPSILON);
        assert_eq!(snapshot.rss_mb, 512);
        assert_eq!(snapshot.limit_mb, 1024);
    }

    #[test]
    fn test_memory_guard_error_display() {
        let err =
            MemoryGuardError::LimitExceeded { current_mb: 2048, limit_mb: 1024, peak_mb: 2100 };
        let msg = err.to_string();
        assert!(msg.contains("2048MB"));
        assert!(msg.contains("1024MB"));
        assert!(msg.contains("2100MB"));

        let err2 = MemoryGuardError::QueryFailed { reason: "test error".to_string() };
        let msg2 = err2.to_string();
        assert!(msg2.contains("test error"));
    }

    #[test]
    fn test_memory_guard_debug() {
        let guard = MemoryGuard::new(2048);
        let debug = format!("{guard:?}");
        assert!(debug.contains("2048"));
        assert!(debug.contains("MemoryGuard"));
    }
}

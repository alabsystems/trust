// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
// Compiler invocation and rewrite loop entry points.
//
// Builds the native trustc command line for single-file vs. targo-driven crate
// invocations, spawns the compiler, streams stderr through the transport parser, and
// renders a VerificationReport. Also hosts the rewrite loop fallback that drives
// prove -> strengthen -> backprop convergence against the in-tree trustc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{env, thread};

use sha2::{Digest as _, Sha256};

use super::backend::{
    TRUST_TARGO_LANE_RUSTFLAGS_ENV, append_codegen_backend_args, append_strict_safety_check_args,
    append_trust_cg_codegen_args, append_verification_mode_args, canonical_rustc_option_name,
    canonicalize_strict_safety_codegen_args, canonicalize_trust_cg_codegen_args,
    encode_lane_rustflags, find_codegen_help_arg, find_forbidden_in_process_codegen_arg,
    inherited_trust_rustflags_warning, lane_rustflags, level_to_num, targo_owned_z_option,
    validate_direct_trust_cg_rlib_target,
};
use super::cargo_selection::{
    CargoSelectionArgs, ResolvedCargoSelection, effective_cargo_target_with_targo,
    preflight_trust_cg_cargo_targets_with_targo, resolve_cargo_selection_with_targo,
    validate_trust_cg_effective_target,
};
use super::discovery::{is_cargo_program, native_trust_cargo_path};
use super::hardened::{
    GateDecision, GateLane, OutcomeCounts, aggregate_coverage, evaluate_run_gate,
    evaluate_verification_gate, hardened_profile_name, hardened_proof_gate_failure_for_results,
    memory_safe_gate_counts, partition_outcome_counts, strict_gate_counts,
};
use super::probe::apply_native_runtime_env;
use super::process_environment::scrub_proof_compiler_authority_env;
use super::project_policy::ProjectRequirementFlags;
use super::provenance::{
    print_runtime_binary_source_backpropagation_blocker,
    runtime_binary_source_provenance_for_rewrite_loop,
};
use super::transport::{
    CargoCompilerEvidence, CargoTargetIdentity, CargoTestExecutable, ParsedCompilerOutput,
    cargo_proof_inventory_report, cargo_report_subject, parse_cargo_json_stdout,
    parse_cargo_json_stdout_for_prepared_tests, parse_cargo_json_stdout_for_test,
    parse_compiler_stderr, parse_untrusted_cargo_stderr,
};
use crate::cli::SubcommandArgs;
use crate::config::TrustConfig;
use crate::process_lifecycle::tree::{collect_process_tree, leads_own_process_group};
#[cfg(test)]
use crate::process_lifecycle::tree::{executable_is_trust_memory_daemon, is_trust_memory_daemon};
use crate::process_lifecycle::{Ownership, StopCause};
use crate::report::{
    CertifiedTestExecutableReport, CertifiedTestExecutionCompletionScope,
    CertifiedTestExecutionPhaseState, CertifiedTestExecutionReport, CompilerDiagnostic,
    LiveCanonicalReport, LiveTransportAuthority, ReportConfig, UnsafeMemoryReportRequest,
    VerificationReport, cargo_active_exclusion_labels, cargo_gate_failing_exclusion_labels,
};
use crate::rewrite_loop::ProofFrontier;
use crate::test_target_panics::TestTargetPanicPolicy;
use crate::types::{OutputFormat, Subcommand, VerificationResult};

mod test_qualification;
use test_qualification::{QualifiedTestExecution, RunGateInputs, finalize_run_gate};
mod retained;
use retained::RunChild;

/// The wall-clock cap on the Cargo TEST EXECUTION phase, held flat (see
/// [`CompilerProcessBounds::flat`]): the harness's stdout is untrusted, so it
/// cannot be allowed to buy idle intervals. It bounds the user's tests, not
/// verification, so it is not one of the backstop's clocks. The verified
/// COMPILER processes are bounded by progress instead, under a ceiling that
/// `[trust] backstop` scales ([`CompilerProcessBounds::from_backstop`]) —
/// since 2026-09-09, when this constant killed first-party/ty's `tla-cli`
/// mid-proof with every unit compiling cleanly.
const COMPILER_PROCESS_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
// A fixed per-process wall-clock cap cannot tell a hung compiler from a big
// one. Trust already bounds what can genuinely hang *inside* the compiler --
// `-Ztrust-verify-function-budget-ms`, the per-obligation
// `-Ztrust-verify-timeout-ms`, and the deadline-independent step budget -- so
// this guard's job is to catch a process that has STOPPED MAKING PROGRESS.
// Progress is every byte drained off the compiler's pipes: the Cargo JSON
// stream and the TRUSTJSON transport both ride stdout/stderr, so a working
// verified compile is continuously observable from out here.
//
// Measured 2026-09-08 on the sealed `trust-dac08891` toolchain, by recovering
// each unit's diagnostic stream from the Cargo fingerprint `output-*` files
// left behind by two runs that the old flat 7200s cap killed:
//   ny `check --allow-l0-gaps --workspace`, 414 units, 15:49:07 -> 17:49:07.
//     ny-propagate lib   3567s / 23579 diagnostics -> mean gap 0.151s
//     ny-core   test-lib 2817s / 18418 diagnostics -> mean gap 0.153s
//     ny-mip    test-lib 4557s / 10086 diagnostics -> mean gap 0.452s (521MB)
//     Last diagnostic landed 8s before the kill.
//   nn `check --allow-l0-gaps --workspace`, 198 units, 11:00:43 -> 13:00:43.
//     nn-cpu lib 7048s / 2956 diagnostics -> mean gap 2.38s
//     nn-dsl lib 2598s / 2868 diagnostics -> mean gap 0.91s
//     Last diagnostic landed 12s before the kill.
// Both processes were streaming ~100KB/s when the cap fired. The longest
// genuinely silent stretch anywhere in either run is a unit's prologue (spawn
// to its first diagnostic): 55s (nn-macros), 37s (ny-levers), 36s (ny-cert).
//
// 30 minutes is ~32x that measured worst-case silence and ~15x the 120s
// per-function verification budget. The measurement covered `check` only:
// codegen and link phases emit nothing and `targo trust build` gates on them,
// and a single large unit can sit in one solver query with no diagnostic to
// print, so the bound is set well above what was observed rather than close
// to it. It is still 4x shorter than the old flat cap, so a compiler that
// truly hangs is caught in 30 minutes instead of 2 hours.
const COMPILER_PROGRESS_IDLE_TIMEOUT: Duration = Duration::from_secs(30 * 60);
// The bound for a process that has produced nothing at all. There is no
// progress signal to be sensitive to yet, so this deliberately stays at the
// historical flat cap: behaviour for a silent process is unchanged.
const COMPILER_SILENT_PROCESS_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
// The absolute ceiling at the builtin backstop (1000 per mille). `[trust]
// backstop` scales it, with the silent and idle bounds above and with the
// per-query and per-function clocks targo passes the compiler, so a run has one
// backstop and one knob (plan §3.2, §3.6; DECISION_QUEUE "T7b"); the three
// process bounds only grow with it, never shrink below these references
// (`CompilerProcessBounds::from_backstop`). Until
// 2026-10-11 it was a second knob, `[trust] compiler_timeout_secs`, which ay
// (72,000 s) and ty (43,200 s) declared; that key is now refused, naming this
// one (`config::RETIRED_CONFIG_KEYS`).
//
// Eight hours is NOT a measured-sufficient ceiling for ay. Its full census fit
// on seal 33 (4h50m) and a two-hour default killed it at 7204.8 s on seal 36,
// but on 2026-09-15 this very eight-hour bound killed `ay-dpll` (lib test) at
// 8h00m00s with 31h45m09s of CPU consumed and output 279 ms old: the watchdog
// judged it alive and only the ceiling fired (ay@03b39a7756). Such a workspace
// raises its root's `backstop` (2,500 gives 20 h); raising this reference
// instead widens every workspace's forged-liveness exposure. Under Cargo the
// guarded process is the `cargo` driver, so today the ceiling bounds the WHOLE
// workspace compile, not one crate; T7's job queue makes it per unit.
//
// Generous but finite. Its only job is to kill a compiler that streams output
// forever and so never goes idle. It has to clear the largest legitimate run
// we have measured -- the ny workspace check above was still emitting at 2h --
// with room for the build and test lanes, which do codegen and linking the two
// measured `check` runs never reached. 8h is 4x the longest observed run and
// ~6x the longest single unit (ny-mip, 4557s).
//
// It is deliberately not 24h. Progress is *any* byte drained off the pipes,
// and in `targo trust test`/`bench` (`cargo_execution_mode`) the untrusted
// test harness's stdout is multiplexed onto that same drained pipe after
// Cargo's build-finished boundary. A `#[test]` looping on `println!` can
// therefore refresh the idle clock forever, and this ceiling is the only thing
// that stops it; every hour here is an hour a forged progress signal can hold
// the gate. Closing that hole properly means gating progress on the
// authenticated prefix of the stream, which this change does not attempt.
const COMPILER_PROCESS_REFERENCE_CEILING: Duration = Duration::from_secs(8 * 60 * 60);
// Output is a proxy for liveness, and a poor one at the top end: a unit deep in
// one solver query prints nothing until it answers, and a cargo leader that has
// stopped scheduling still loops until its in-flight children drain
// (src/tools/targo/src/cargo/core/compiler/job_queue/mod.rs). Consumed CPU is
// the better signal -- a process that is working burns it, a hung one does not
// -- so the idle bound now needs BOTH to be stale. These bound how often that
// CPU sample may be taken; the effective interval is the shorter of the ceiling
// and an eighth of the idle bound, so a test with a sub-second bound still gets
// several samples inside it while the shipped 30-minute bound samples twice a
// minute.
const COMPILER_CPU_SAMPLE_INTERVAL: Duration = Duration::from_secs(30);
const COMPILER_CPU_SAMPLE_MIN_INTERVAL: Duration = Duration::from_millis(20);
// How much CPU a group must consume between two samples before that counts as
// work. A compiler that is computing burns close to a core, i.e. most of a
// sampling interval's worth of CPU per interval -- 30000x this at the shipped
// interval. A blocked process burns none, but it can still be woken by a timer
// or a signal and charged a few microseconds, and reading that as "working"
// would hand a hung process an unbounded reprieve. 1ms sits between the two
// with orders of magnitude to spare in both directions.
const COMPILER_CPU_ADVANCE_MIN: Duration = Duration::from_millis(1);
// How long the evidence pipes may stay OPEN after the compiler leader exited.
//
// This is a containment bound, not a parsing one. The leader is reaped; every
// write end should have gone with it; anything still holding one is a process
// that outlived its own containment, and 30s is generous for the close to
// propagate. What happens on the READ side afterwards -- a parser working
// through hundreds of thousands of retained transport lines, which is minutes
// at ay's scale -- is not bounded by this and must not be: see
// `receive_compiler_output`, and the 2026-09-18 measurement recorded there.
const COMPILER_OUTPUT_CLOSE_TIMEOUT: Duration = Duration::from_secs(30);
/// Liveness backstop for the parse that runs AFTER end-of-file, which is not a
/// containment question -- see the argument in `receive_compiler_output_within`.
///
/// This exists only so that a parser which neither returns nor unwinds cannot
/// hang a release gate forever. It must therefore be far above any parse a real
/// build can produce: at the 2026-09-19 measurement of ~25.9 ms per MB of
/// retained transport, twenty minutes is ~46 GB, and a run cannot retain that
/// much (the transport ceiling is memory/8, 16 GiB on this box). A run that
/// trips it has found a bug in this crate, and the refusal says exactly that.
const POST_EOF_PARSE_LIVENESS_BOUND: Duration = Duration::from_secs(20 * 60);

const CERTIFIED_TEST_EXECUTION_PLATFORM_BLOCKER: &str = "evidence-grade Cargo test execution \
requires Linux sealed-memfd execveat or macOS suspended CDHash-authenticated execution on \
x86-64/aarch64; this platform has no implemented authenticated launch backend";

fn certified_test_execution_platform_blocker_for(
    target_os: &str,
    target_arch: &str,
) -> Option<&'static str> {
    if matches!(target_os, "linux" | "macos") && matches!(target_arch, "x86_64" | "aarch64") {
        None
    } else {
        Some(CERTIFIED_TEST_EXECUTION_PLATFORM_BLOCKER)
    }
}

fn certified_test_execution_platform_blocker() -> Option<&'static str> {
    certified_test_execution_platform_blocker_for(std::env::consts::OS, std::env::consts::ARCH)
}

fn record_certified_test_execution_error(
    execution: Option<&mut CertifiedTestExecutionReport>,
    phase_b_started: bool,
    error: &str,
) {
    if let Some(execution) = execution {
        execution.phase_b_state = if phase_b_started {
            CertifiedTestExecutionPhaseState::Started
        } else {
            CertifiedTestExecutionPhaseState::Blocked
        };
        execution.phase_b_exit = None;
        execution.blocker = Some(error.to_string());
    }
}

/// The wall-clock bounds one compiler process is held to. The idle bound is
/// measured from the last observed progress, not from process start.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CompilerProcessBounds {
    /// Cap on a process that has produced no output at all.
    silent: Duration,
    /// Cap on the interval between two observed progress events, applied only
    /// once at least one byte has been drained.
    idle: Duration,
    /// Cap on total wall clock regardless of progress.
    absolute: Duration,
}

impl CompilerProcessBounds {
    #[cfg(test)]
    const DEFAULT: Self = Self {
        silent: COMPILER_SILENT_PROCESS_TIMEOUT,
        idle: COMPILER_PROGRESS_IDLE_TIMEOUT,
        absolute: COMPILER_PROCESS_REFERENCE_CEILING,
    };

    /// The bounds for one verified compiler process under the run's backstop
    /// (`[trust] backstop`, per mille): each reference bound times `b / 1000`,
    /// never below the reference. At the builtin 1000 and below they are the
    /// reference bounds exactly (2 h silent, 30 min idle, 8 h absolute); 2,500
    /// gives the 20 h ay used to declare. One factor scales all three, so the
    /// silent and idle bounds stay under the absolute one without a clamp. A
    /// process one of them ends could not run (exit 3).
    ///
    /// The floor (T7b-BACKSTOP-1): under Cargo the guarded process is the
    /// whole `cargo` driver, so a backstop below 1000 — an experiment on the
    /// solver clocks, such as the determinism acceptance's `backstop = 1`
    /// negative control, which must reach a report whose rows read
    /// `wall-backstop` — would otherwise kill every real build in seconds and
    /// leave nothing to read. Until T7's job queue bounds each unit, a smaller
    /// backstop only shortens the per-query and per-function clocks.
    fn from_backstop(backstop: trust_types::determinism::Backstop) -> Self {
        let per_mille =
            backstop.per_mille.max(trust_types::determinism::Backstop::BUILTIN.per_mille);
        let scale = |reference: Duration| reference.saturating_mul(per_mille) / 1000;
        Self {
            silent: scale(COMPILER_SILENT_PROCESS_TIMEOUT),
            idle: scale(COMPILER_PROGRESS_IDLE_TIMEOUT),
            absolute: scale(COMPILER_PROCESS_REFERENCE_CEILING),
        }
    }

    /// Every bound collapsed onto one duration: the pre-watchdog flat-cap
    /// shape. The Cargo test-execution phase uses it, since its drained
    /// output is the untrusted harness's; tests use it to pin one deadline.
    const fn flat(timeout: Duration) -> Self {
        Self { silent: timeout, idle: timeout, absolute: timeout }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompilerTimeoutBound {
    Silent,
    Idle,
    Absolute,
}

/// What the CPU sampler knew about the child's process TREE when a bound was
/// evaluated. `Unsampled` is an ABSENT observation, never a stall: it covers a
/// platform with no sampler, a child that never led its own process group, and
/// a read that failed. Every consumer must treat it as "this signal said
/// nothing", which is exactly the output-only guard that shipped before.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompilerCpuEvidence {
    Unsampled,
    Sampled {
        /// Total CPU consumed by every process the tree has held, including
        /// members that have since exited, at the last successful sample.
        consumed: Duration,
        /// How long ago that total last rose by at least
        /// `COMPILER_CPU_ADVANCE_MIN`.
        since_advance: Duration,
    },
}

/// Which bound fired and what the clocks read when it did. `"exceeded the
/// 7200s timeout"` told a reader nothing about whether the compiler was
/// working; every message below names the bound and the measured durations.
#[derive(Clone, Copy, Debug)]
struct CompilerTimeoutDetail {
    bound: CompilerTimeoutBound,
    /// The bound that fired.
    limit: Duration,
    /// Wall clock since the process was spawned.
    elapsed: Duration,
    /// How long ago the last byte was drained (or, before any byte, how long
    /// the process has been silent -- the same number as `elapsed`). This is
    /// the OUTPUT clock only; the bound is compared against the more recent of
    /// this and the CPU clock, which `cpu` carries.
    idle: Duration,
    /// The configured idle bound, so the absolute-bound message can say what
    /// the compiler was outrunning.
    idle_limit: Duration,
    /// The other half of the liveness picture, so a killed build can say
    /// whether the process was consuming CPU while it was quiet.
    cpu: CompilerCpuEvidence,
}

/// Render a bound or a measurement the way an operator sizes up a build log.
/// `{:?}` prints the 8h ceiling as `28800s` and a two-hour elapsed as
/// `7231.418902341s`; neither tells a reader at a glance how long the compiler
/// had been working, which is the whole point of these messages.
fn format_bound_duration(duration: Duration) -> String {
    let seconds = duration.as_secs();
    let (hours, minutes, seconds) = (seconds / 3600, (seconds % 3600) / 60, seconds % 60);
    if hours > 0 {
        format!("{hours}h{minutes:02}m{seconds:02}s")
    } else if minutes > 0 {
        format!("{minutes}m{seconds:02}s")
    } else if seconds > 0 {
        format!("{seconds}s")
    } else {
        format!("{}ms", duration.as_millis())
    }
}

impl CompilerTimeoutDetail {
    fn message(&self) -> String {
        let limit = format_bound_duration(self.limit);
        let elapsed = format_bound_duration(self.elapsed);
        let idle = format_bound_duration(self.idle);
        match self.bound {
            CompilerTimeoutBound::Silent => format!(
                "compiler process produced no output at all within the {limit} silent-process bound (ran {elapsed}); \
                 no progress was ever observed, so the idle bound never armed"
            ),
            CompilerTimeoutBound::Idle => match self.cpu {
                CompilerCpuEvidence::Sampled { consumed, since_advance } => format!(
                    "compiler process stopped making progress: nothing was drained from its stdout/stderr for \
                     {idle} and its process tree consumed no CPU for {} (having consumed {} of CPU in total), \
                     exceeding the {limit} idle bound (the process had been running {elapsed})",
                    format_bound_duration(since_advance),
                    format_bound_duration(consumed)
                ),
                CompilerCpuEvidence::Unsampled => format!(
                    "compiler process stopped making progress: nothing was drained from its stdout/stderr for \
                     {idle}, exceeding the {limit} idle bound (the process had been running {elapsed}); its CPU \
                     time could not be sampled, so output was the only liveness signal"
                ),
            },
            CompilerTimeoutBound::Absolute => match self.cpu {
                CompilerCpuEvidence::Sampled { consumed, since_advance } => format!(
                    "compiler process exceeded the {limit} absolute bound (ran {elapsed}, last output {idle} ago, \
                     {} of CPU consumed, last CPU advance {} ago); it kept showing liveness -- output or CPU -- so \
                     the {} idle bound never fired",
                    format_bound_duration(consumed),
                    format_bound_duration(since_advance),
                    format_bound_duration(self.idle_limit)
                ),
                CompilerCpuEvidence::Unsampled => format!(
                    "compiler process exceeded the {limit} absolute bound (ran {elapsed}, last output {idle} ago); \
                     it kept producing output, so the {} idle bound never fired",
                    format_bound_duration(self.idle_limit)
                ),
            },
        }
    }
}

/// Evidence that the compiler is alive, published by the pipe drains.
struct CompilerProgress {
    start: Instant,
    /// Nanoseconds since `start` at the last drained byte, biased by one so
    /// that zero means "nothing has been drained yet".
    last_plus_one: AtomicU64,
}

impl CompilerProgress {
    fn new() -> Self {
        Self { start: Instant::now(), last_plus_one: AtomicU64::new(0) }
    }

    fn record(&self) {
        let nanos = u64::try_from(self.start.elapsed().as_nanos()).unwrap_or(u64::MAX);
        self.last_plus_one.store(nanos.saturating_add(1), Ordering::Release);
    }

    /// `None` until the first byte is drained.
    fn last_progress(&self) -> Option<Duration> {
        match self.last_plus_one.load(Ordering::Acquire) {
            0 => None,
            biased => Some(Duration::from_nanos(biased - 1)),
        }
    }
}

/// Reads one process's consumed CPU, with whatever conversion constant the
/// platform needs resolved once per sample instead of once per process.
#[cfg(target_os = "macos")]
struct CpuClock {
    numer: u128,
    denom: u128,
}

// `libc` deprecates its `mach_timebase_info` binding in favour of the `mach2`
// crate. Adding a crate to this graph for one struct and one call is not worth
// it, the binding is a straight FFI declaration of a stable Mach entry point,
// and libc still ships it. The allow is scoped to this impl so nothing else in
// the file inherits it.
#[cfg(target_os = "macos")]
#[allow(deprecated)]
impl CpuClock {
    fn resolve() -> Option<Self> {
        let mut timebase = std::mem::MaybeUninit::<libc::mach_timebase_info>::zeroed();
        if unsafe { libc::mach_timebase_info(timebase.as_mut_ptr()) } != 0 {
            return None;
        }
        let timebase = unsafe { timebase.assume_init() };
        if timebase.denom == 0 {
            return None;
        }
        Some(Self { numer: u128::from(timebase.numer), denom: u128::from(timebase.denom) })
    }

    /// Nanoseconds of user plus system CPU `pid` has consumed. `None` covers a
    /// process that exited between enumeration and inspection, which reads
    /// short; the accumulator treats that as "contributes nothing further",
    /// never as a decrease.
    fn read(&self, pid: u32) -> Option<u64> {
        let pid = libc::pid_t::try_from(pid).ok()?;
        let info_size = libc::c_int::try_from(std::mem::size_of::<libc::proc_taskinfo>()).ok()?;
        let mut info = std::mem::MaybeUninit::<libc::proc_taskinfo>::zeroed();
        let read = unsafe {
            libc::proc_pidinfo(pid, libc::PROC_PIDTASKINFO, 0, info.as_mut_ptr().cast(), info_size)
        };
        if read != info_size {
            return None;
        }
        let info = unsafe { info.assume_init() };
        // `pti_total_user`/`pti_total_system` are Mach absolute time units, NOT
        // nanoseconds: this machine's timebase is 125/3, and treating the raw
        // value as nanoseconds understates CPU by 41x. Converted, it matches
        // `getrusage(RUSAGE_SELF)` to four decimal places (measured 2026-09-09:
        // 2.9318s both ways over a 3.5s spin).
        let units =
            u128::from(info.pti_total_user).saturating_add(u128::from(info.pti_total_system));
        Some(u64::try_from(units * self.numer / self.denom).unwrap_or(u64::MAX))
    }
}

#[cfg(target_os = "linux")]
struct CpuClock {
    ticks_per_second: u128,
}

#[cfg(target_os = "linux")]
impl CpuClock {
    fn resolve() -> Option<Self> {
        let ticks = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
        if ticks <= 0 {
            return None;
        }
        Some(Self { ticks_per_second: u128::try_from(ticks).ok()? })
    }

    fn read(&self, pid: u32) -> Option<u64> {
        let stat = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
        // `comm` is parenthesised and may itself contain spaces and `)`, so the
        // numeric fields start after the LAST `)`.
        let tail = stat.rfind(')').and_then(|end| stat.get(end + 1..))?;
        let fields: Vec<&str> = tail.split_ascii_whitespace().collect();
        // Indices relative to `tail`: 0 state, 1 ppid, 2 pgrp, 11 utime, 12 stime.
        if fields.len() < 13 {
            return None;
        }
        let utime = fields[11].parse::<u64>().ok()?;
        let stime = fields[12].parse::<u64>().ok()?;
        let ticks = u128::from(utime).saturating_add(u128::from(stime));
        Some(u64::try_from(ticks * 1_000_000_000 / self.ticks_per_second).unwrap_or(u64::MAX))
    }
}

/// No dependency-free per-pid CPU reading exists here. `resolve` returning
/// `None` is what makes every sample on such a target an absent observation.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
struct CpuClock;

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
impl CpuClock {
    fn resolve() -> Option<Self> {
        None
    }

    fn read(&self, _pid: u32) -> Option<u64> {
        None
    }
}

/// Per-pid CPU readings for the process TREE rooted at a driver, with the
/// scratch buffers owned across samples so a steady-state sample allocates
/// nothing.
///
/// The tree, not the process group, is the unit, and the process group is not
/// merely a weaker choice -- it is the wrong set. `cargo-util`'s
/// `process_builder.rs:1237` spawns every compiler with
/// `command.process_group(0)`, so each `trustc` LEAVES the driver's group the
/// instant it execs. Measured against a live verified check on 2026-09-09:
/// `proc_listpgrppids` on the driver listed exactly ONE member, the driver
/// itself, holding 15.9s of CPU, while the 18 `trustc` processes hanging off it
/// held 7,834s between them and were burning about twelve cores. Over five
/// minutes the children advanced 3,725s -> 5,136s while the group reading the
/// watchdog was using moved 10.6s -> 11.1s.
///
/// That is not just a small signal. The driver's own CPU is spent draining its
/// children's output, so "nothing was drained" and "the group consumed no CPU"
/// are the same observation twice, and the idle bound -- which arms only when
/// BOTH are stale -- was ANDing one clock with itself. It killed a check whose
/// in-flight unit had consumed 7,254s of CPU over 7,191s of wall clock, 100.9%
/// mean utilisation, while reporting "consumed no CPU for 30m00s".
///
/// Widening the process group instead would be the wrong repair: per-compiler
/// group isolation is what makes a rejected compiler's own descendants killable
/// without killing unrelated work, which `cargo-util` says at its call site and
/// `trust-os/src/process.rs` says at length.
///
/// What a tree walk cannot see: a descendant that double-forks is reparented to
/// init and has no path back to the root, so it is invisible here exactly as it
/// is to every other pid-based containment on Unix. Only a job object, a
/// cgroup, or a PID namespace closes that, and none of the three is available
/// to this crate on macOS.
struct ProcessTreeCpuSampler {
    tree: Vec<u32>,
    reading: Vec<(u32, u64)>,
}

impl ProcessTreeCpuSampler {
    fn new() -> Self {
        Self { tree: Vec::new(), reading: Vec::new() }
    }

    /// Refresh [`Self::reading`] with `(pid, nanoseconds)` for every member of
    /// the tree rooted at `root` that could be read, sorted by pid.
    ///
    /// `false` means "no reading", never "no work". Callers must treat it as an
    /// absent observation -- see `CompilerCpuAccumulator::observe` and
    /// `CompilerCpuLiveness::observe`, which store nothing then, so a broken
    /// sampler is neither read as a stall nor able to keep a dead process
    /// alive.
    fn sample(&mut self, root: u32) -> bool {
        self.reading.clear();
        if !leads_own_process_group(root) {
            return false;
        }
        let Some(clock) = CpuClock::resolve() else {
            return false;
        };
        if !collect_process_tree(root, &mut self.tree) {
            return false;
        }
        for &member in &self.tree {
            if let Some(nanos) = clock.read(member) {
                self.reading.push((member, nanos));
            }
        }
        // Sorted so the accumulator can look a pid up by binary search rather
        // than scanning, and so the reading is stable to compare in tests.
        self.reading.sort_unstable_by_key(|&(pid, _)| pid);
        !self.reading.is_empty()
    }

    fn reading(&self) -> &[(u32, u64)] {
        &self.reading
    }
}

/// Total CPU consumed by everything that has EVER been in the tree, kept
/// monotone across members that exit.
///
/// Summing the live members is not enough, and the gap is not a corner case.
/// Measured on the same live check on 2026-09-09, the tree's live sum went
/// 6,835.4s -> 4,257.1s across two samples a minute apart -- a fall of 2,578s
/// -- purely because compilers finished and left. A rule of the form "the
/// summed CPU of the currently live set advanced" reads that minute, during
/// which twelve cores were busy, as no advance at all; and it does so most
/// often exactly when the build is completing the most units. Fixing WHICH
/// processes are seen does not fix that. Only accumulating does.
///
/// So each pid is differenced against its OWN previous reading and only
/// non-negative deltas are added. A pid that vanishes stops contributing but
/// cannot subtract what it already contributed, and a pid seen for the first
/// time contributes its whole reading, which is CPU it burned inside this tree.
/// The total is monotone by construction, which is what lets
/// `CompilerCpuLiveness::observe` read any rise as work.
///
/// The cheaper alternative -- call it progress if a new pid appeared or any one
/// pid's own CPU rose, without summing -- is equally immune to the falling sum,
/// but it throws away the number the timeout message needs. "having consumed
/// 32s of CPU in total" is what made this defect diagnosable at all; a boolean
/// would have said nothing. Accumulating keeps the liveness rule and the
/// evidence in one number.
struct CompilerCpuAccumulator {
    sampler: ProcessTreeCpuSampler,
    /// Last reading, in nanoseconds, for each pid still in the tree. Bounded by
    /// `MAX_PROCESS_TREE_MEMBERS` because the sampler is, and pruned every
    /// sample so a build's thousands of finished compilers cannot grow it.
    per_pid: BTreeMap<u32, u64>,
    /// Sum of every non-negative per-pid delta ever observed, in nanoseconds.
    accumulated: u64,
}

impl CompilerCpuAccumulator {
    fn new() -> Self {
        Self { sampler: ProcessTreeCpuSampler::new(), per_pid: BTreeMap::new(), accumulated: 0 }
    }

    /// Take one reading and fold it in. `None` means "no reading", never "no
    /// work": nothing is stored, so the caller's clocks are neither refreshed
    /// nor reset.
    fn observe(&mut self, root: u32) -> Option<u64> {
        if !self.sampler.sample(root) {
            return None;
        }
        for &(pid, nanos) in self.sampler.reading() {
            match self.per_pid.get_mut(&pid) {
                // A reading that FELL for one pid means the pid was recycled,
                // not that a process un-burned CPU. Re-base on the new value
                // rather than credit a negative delta.
                Some(previous) => {
                    self.accumulated =
                        self.accumulated.saturating_add(nanos.saturating_sub(*previous));
                    *previous = nanos;
                }
                None => {
                    self.accumulated = self.accumulated.saturating_add(nanos);
                    self.per_pid.insert(pid, nanos);
                }
            }
        }
        // Drop members that have left the tree. Their CPU stays banked in
        // `accumulated`; keeping their entries would both grow the map without
        // bound and let a recycled pid be differenced against a stranger.
        let reading = self.sampler.reading();
        self.per_pid.retain(|pid, _| reading.binary_search_by_key(pid, |&(pid, _)| pid).is_ok());
        Some(self.accumulated)
    }
}

/// How many surviving descendants one containment diagnostic will name, and how
/// much of each one's argv it will render.
///
/// The walk itself is already bounded by [`MAX_PROCESS_TREE_MEMBERS`]; these
/// bound the MESSAGE, which an operator has to read. Sixty-four is far past the
/// handful of direct children a verified run has (one `trustd`, plus whatever a
/// concurrent test fixture holds) while still being a list rather than a dump.
const MAX_NAMED_SURVIVING_DESCENDANTS: usize = 64;
const MAX_RENDERED_ARGV_BYTES: usize = 160;

/// One process's argv, space-joined, or `None` when this platform or this
/// process will not give it up.
///
/// This is diagnostic-only. A failure to read it must never change a verdict,
/// so every error path returns `None` and the caller prints the pid alone.
#[cfg(target_os = "macos")]
fn process_argv(pid: u32) -> Option<String> {
    // `KERN_PROCARGS2` returns `[argc: i32][exec_path\0][\0 padding][argv...]`.
    // Everything before the first argv string is layout, not arguments, so the
    // exec path is skipped and the strings after it are taken by count.
    let Ok(pid) = libc::c_int::try_from(pid) else { return None };
    let mut mib = [libc::CTL_KERN, libc::KERN_PROCARGS2, pid];
    let mut size: libc::size_t = 0;
    // SAFETY: a 3-entry MIB with a null output pointer is the documented
    // size-query form; it writes only `size`.
    if unsafe {
        libc::sysctl(mib.as_mut_ptr(), 3, std::ptr::null_mut(), &mut size, std::ptr::null_mut(), 0)
    } != 0
    {
        return None;
    }
    // ARG_MAX is 1 MiB here. Refusing anything larger bounds this allocation
    // without needing to trust the value the kernel just reported.
    if size < std::mem::size_of::<u32>() || size > 1 << 20 {
        return None;
    }
    let mut buffer = vec![0u8; size];
    // SAFETY: `buffer` has exactly `size` bytes, which is what the query above
    // reported, and `sysctl` writes at most that many.
    if unsafe {
        libc::sysctl(
            mib.as_mut_ptr(),
            3,
            buffer.as_mut_ptr().cast(),
            &mut size,
            std::ptr::null_mut(),
            0,
        )
    } != 0
    {
        return None;
    }
    buffer.truncate(size);
    let count: [u8; 4] = buffer.get(..4)?.try_into().ok()?;
    let argc = usize::try_from(u32::from_ne_bytes(count)).ok()?;
    let rest = buffer.get(4..)?;
    // The exec path, then the NUL padding that aligns what follows it.
    let exec_end = rest.iter().position(|byte| *byte == 0)?;
    let tail = rest.get(exec_end..)?;
    let first_argument = tail.iter().position(|byte| *byte != 0)?;
    Some(join_nul_separated_argv(tail.get(first_argument..)?, Some(argc)))
}

/// The same argv, read from `/proc`, where it is already NUL-separated and
/// carries no exec-path prefix or padding.
#[cfg(target_os = "linux")]
fn process_argv(pid: u32) -> Option<String> {
    use std::io::Read as _;

    let mut file = File::open(format!("/proc/{pid}/cmdline")).ok()?;
    let mut buffer = Vec::new();
    // Same 1 MiB ceiling as the macOS path, for the same reason.
    file.take(1 << 20).read_to_end(&mut buffer).ok()?;
    Some(join_nul_separated_argv(&buffer, None))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn process_argv(_pid: u32) -> Option<String> {
    None
}

/// Render at most `limit` NUL-separated arguments as one bounded line.
///
/// `limit` is the kernel-reported `argc` on the platform that reports one; the
/// byte ceiling applies regardless, so neither a huge argv nor a miscounted one
/// can make this string unbounded.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn join_nul_separated_argv(bytes: &[u8], limit: Option<usize>) -> String {
    let mut rendered = String::new();
    let mut taken = 0usize;
    let mut truncated = false;
    for argument in bytes.split(|byte| *byte == 0) {
        if argument.is_empty() {
            continue;
        }
        if limit.is_some_and(|limit| taken >= limit) {
            break;
        }
        taken += 1;
        if !rendered.is_empty() {
            rendered.push(' ');
        }
        rendered.push_str(&String::from_utf8_lossy(argument));
        if rendered.len() > MAX_RENDERED_ARGV_BYTES {
            truncated = true;
            break;
        }
    }
    if truncated {
        // A char boundary, not a byte one: an argv can hold any UTF-8.
        let mut end = MAX_RENDERED_ARGV_BYTES.min(rendered.len());
        while end > 0 && !rendered.is_char_boundary(end) {
            end -= 1;
        }
        rendered.truncate(end);
        rendered.push_str("...");
    }
    rendered
}

/// Name every process still descending from THIS one, with its argv.
///
/// A diagnostic that says an uncontained descendant "may" own something,
/// without saying which, cannot be checked and cannot be acted on. This is what
/// makes the claim falsifiable: either it names a process an operator can go
/// look at, or it says plainly that it found none, which is itself the useful
/// observation -- a holder that is not here escaped this tree.
///
/// The root is this process, not the compiler leader: by the time a
/// close-timeout fires the leader has been reaped, so its pid names nothing
/// (and could name a stranger after recycling). What a pid walk cannot see is a
/// descendant that was reparented onto init when the leader exited; that limit
/// is stated in the message rather than papered over, and it is the same limit
/// the stop path (`process_lifecycle::stop_tree`) documents.
///
/// The walk is [`collect_process_tree`], the watchdog's, and on this branch it
/// never includes the machine-wide `trustd` (nor a process whose executable
/// image cannot be read): see [`is_trust_memory_daemon`]. That exclusion exists
/// so no kill can reach the host's memory authority, and it is kept here rather
/// than weakened for a diagnostic, so the rendered clause says in words that
/// the daemon is not in the list and names the tool that can check it.
///
/// `None` means the walk itself is unavailable here, which is a different
/// statement from "nobody is there" and is reported as one.
fn surviving_descendants() -> SurvivingDescendants {
    let mut tree = Vec::new();
    let own = std::process::id();
    if !collect_process_tree(own, &mut tree) {
        return SurvivingDescendants::Unavailable;
    }
    // The stop sentinel is this process's child by design and holds none of
    // its pipes (`process_lifecycle::sentinel`), so it is never a suspect.
    let sentinel = crate::process_lifecycle::sentinel::sentinel_pid();
    tree.retain(|member| *member != own && Some(*member) != sentinel);
    let total = tree.len();
    let members = tree
        .into_iter()
        .take(MAX_NAMED_SURVIVING_DESCENDANTS)
        .map(|pid| SurvivingProcess { pid, argv: process_argv(pid) })
        .collect();
    SurvivingDescendants::Walked { members, truncated: total > MAX_NAMED_SURVIVING_DESCENDANTS }
}

/// One process a containment diagnostic can point an operator at.
struct SurvivingProcess {
    pid: u32,
    /// `None` where this platform, or this process, will not report it.
    argv: Option<String>,
}

/// What a walk of this process's descendants found. `Unavailable` and an empty
/// `Walked` are deliberately different: "the walk does not work here" and
/// "the walk ran and found nobody" support different conclusions.
enum SurvivingDescendants {
    Unavailable,
    Walked { members: Vec<SurvivingProcess>, truncated: bool },
}

/// Appended to every walked clause: the walk skips `trustd` by construction
/// (see [`surviving_descendants`]), and a list that silently omitted the one
/// long-lived process a run starts would be read as clearing it.
const DAEMON_EXCLUDED_FROM_WALK: &str = "the machine-wide `trustd` is never a member of this \
walk (it is excluded so no watchdog kill can reach it), so check it with `lsof -p` if it is \
suspected";

/// Render [`surviving_descendants`] as one clause of a containment diagnostic.
fn render_surviving_descendants(descendants: &SurvivingDescendants) -> String {
    let SurvivingDescendants::Walked { members: descendants, truncated } = descendants else {
        return "this platform has no process-tree walk, so no holder can be named from here -- \
                find it with `lsof`/`fuser` on the pipe"
            .to_string();
    };
    if descendants.is_empty() {
        return format!(
            "no process still descends from this one, so nothing reachable from here holds it \
             -- a holder that was reparented onto init when the leader exited is invisible to a \
             pid walk and has to be found with `lsof`/`fuser` on the pipe; \
             {DAEMON_EXCLUDED_FROM_WALK}"
        );
    }
    let mut rendered = String::from("surviving descendants of this run: ");
    for (index, member) in descendants.iter().enumerate() {
        if index > 0 {
            rendered.push_str("; ");
        }
        let pid = member.pid;
        match &member.argv {
            Some(argv) if !argv.is_empty() => rendered.push_str(&format!("pid {pid} `{argv}`")),
            _ => rendered.push_str(&format!("pid {pid} (argv unavailable)")),
        }
    }
    if *truncated {
        rendered.push_str("; list truncated");
    }
    rendered.push_str("; ");
    rendered.push_str(DAEMON_EXCLUDED_FROM_WALK);
    rendered
}

/// The CPU half of the liveness picture, sampled by whichever thread is
/// enforcing the bounds. Output liveness is pushed by the drains
/// (`CompilerProgress`); this one has to be pulled, so it carries its own rate
/// limit rather than trusting every caller to hold one.
struct CompilerCpuLiveness {
    /// The driver's pid, which `process_lifecycle::configure_own_group` also makes its pgid.
    /// It is the ROOT of the sampled tree; the group it leads is only a part
    /// of that tree, and on a real cargo run it is the part with no compiler
    /// in it.
    driver: u32,
    /// Lower bound on the spacing between two samples, and the cap `poll`
    /// puts on the interval it hands out -- so the watchdog wakes at least
    /// this often, which is what makes the samples happen at all.
    interval: Duration,
    /// Nanoseconds since the guard started at the last sample ATTEMPT, biased
    /// by one so that zero means "never attempted".
    sampled_plus_one: AtomicU64,
    /// The last successfully read ACCUMULATED total, in nanoseconds of CPU,
    /// biased by one so that zero means "never read".
    consumed_plus_one: AtomicU64,
    /// Nanoseconds since the guard started at the last observed advance of
    /// that total, biased by one.
    advanced_plus_one: AtomicU64,
    /// The per-pid state that total is built from. Behind a mutex because
    /// `CompilerTimeoutState` is shared between the watchdog thread and the
    /// portable waiter; a poisoned lock reads as "no reading", which is the
    /// same neutral degradation as a failed sample.
    accumulator: Mutex<CompilerCpuAccumulator>,
}

impl CompilerCpuLiveness {
    fn new(driver: u32, bounds: CompilerProcessBounds) -> Self {
        // Several samples have to fit inside the idle bound or the CPU signal
        // could never refresh it before it fired; an eighth of the bound gives
        // eight chances. The ceiling keeps the shipped 30-minute bound from
        // sampling once every four minutes, and the floor keeps a test's
        // sub-second bound from sampling in a spin.
        let interval =
            (bounds.idle / 8).clamp(COMPILER_CPU_SAMPLE_MIN_INTERVAL, COMPILER_CPU_SAMPLE_INTERVAL);
        Self {
            driver,
            interval,
            sampled_plus_one: AtomicU64::new(0),
            consumed_plus_one: AtomicU64::new(0),
            advanced_plus_one: AtomicU64::new(0),
            accumulator: Mutex::new(CompilerCpuAccumulator::new()),
        }
    }

    fn nanos(duration: Duration) -> u64 {
        u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
    }

    /// Take at most one sample per `interval`, `now` being the elapsed time
    /// the caller already measured.
    ///
    /// A failed read stores NOTHING. It does not refresh the CPU clock, which
    /// would let an unreadable sample keep a hung process alive; and it does
    /// not reset it, which would read a broken sampler as a stall. Those are
    /// the two ways this could become a new failure mode, and neutrality is
    /// the only direction that is neither: a platform where every read fails
    /// degrades to precisely the output-only guard that shipped before, so the
    /// idle bound still fires on a hang.
    fn observe(&self, now: Duration) {
        let now_nanos = Self::nanos(now);
        let attempted = self.sampled_plus_one.load(Ordering::Acquire);
        if attempted != 0 && now_nanos.saturating_sub(attempted - 1) < Self::nanos(self.interval) {
            return;
        }
        self.sampled_plus_one.store(now_nanos.saturating_add(1), Ordering::Release);
        // A poisoned lock is exactly as informative as a failed read, and is
        // handled the same way: store nothing.
        let Some(consumed) = self
            .accumulator
            .lock()
            .ok()
            .and_then(|mut accumulator| accumulator.observe(self.driver))
        else {
            return;
        };
        let consumed = consumed.saturating_add(1);
        let previous = self.consumed_plus_one.swap(consumed, Ordering::AcqRel);
        // The accumulated total is monotone by construction -- see
        // `CompilerCpuAccumulator` for why the naive live sum is not -- so
        // `previous` is a true baseline and any rise is true work.
        //
        // The baseline moves on EVERY successful sample, deliberately: that
        // makes `COMPILER_CPU_ADVANCE_MIN` a RATE, 1ms per sampling interval,
        // rather than a lifetime total. A genuinely hung process charged a few
        // microseconds each time a timer wakes it would otherwise accumulate
        // its way past a fixed threshold over a 30-minute bound and buy itself
        // another one.
        if previous == 0
            || consumed >= previous.saturating_add(Self::nanos(COMPILER_CPU_ADVANCE_MIN))
        {
            self.advanced_plus_one.store(now_nanos.saturating_add(1), Ordering::Release);
        }
    }

    fn evidence(&self, now: Duration) -> CompilerCpuEvidence {
        let consumed = self.consumed_plus_one.load(Ordering::Acquire);
        let advanced = self.advanced_plus_one.load(Ordering::Acquire);
        if consumed == 0 || advanced == 0 {
            return CompilerCpuEvidence::Unsampled;
        }
        CompilerCpuEvidence::Sampled {
            consumed: Duration::from_nanos(consumed - 1),
            since_advance: now.saturating_sub(Duration::from_nanos(advanced - 1)),
        }
    }
}

/// The shared clock the watchdog thread and the portable waiter both read.
struct CompilerTimeoutState {
    bounds: CompilerProcessBounds,
    progress: Arc<CompilerProgress>,
    cpu: CompilerCpuLiveness,
    timed_out: AtomicBool,
    detail: Mutex<Option<CompilerTimeoutDetail>>,
    retained_phase: Mutex<RetainedProcessPhase>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RetainedProcessPhase {
    Compiling,
    Qualifying,
    Executing { absolute_deadline: Duration },
}

impl CompilerTimeoutState {
    fn new(pid: u32, bounds: CompilerProcessBounds) -> Self {
        Self {
            bounds,
            progress: Arc::new(CompilerProgress::new()),
            cpu: CompilerCpuLiveness::new(pid, bounds),
            timed_out: AtomicBool::new(false),
            detail: Mutex::new(None),
            retained_phase: Mutex::new(RetainedProcessPhase::Compiling),
        }
    }

    fn enter_qualification(&self) -> Result<(), String> {
        if self.timed_out() || self.progress.start.elapsed() >= self.bounds.absolute {
            return Err("the original compiler deadline expired before qualification".into());
        }
        let mut phase = self.retained_phase.lock().map_err(|_| "retained phase lock poisoned")?;
        if *phase != RetainedProcessPhase::Compiling {
            return Err("compiler checkpoint was already consumed".into());
        }
        *phase = RetainedProcessPhase::Qualifying;
        Ok(())
    }

    fn enter_execution(&self, cap: Duration) -> Result<(), String> {
        if self.timed_out() || self.progress.start.elapsed() >= self.bounds.absolute {
            return Err("the original compiler deadline expired before execution".into());
        }
        let mut phase = self.retained_phase.lock().map_err(|_| "retained phase lock poisoned")?;
        if *phase != RetainedProcessPhase::Qualifying {
            return Err("retained execution requires the current compile checkpoint".into());
        }
        // Keep the process's original absolute ceiling. Neither frontend proof
        // qualification nor untrusted harness output can restart that clock.
        let absolute_deadline =
            self.progress.start.elapsed().saturating_add(cap).min(self.bounds.absolute);
        *phase = RetainedProcessPhase::Executing { absolute_deadline };
        Ok(())
    }

    fn absolute_deadline(&self) -> Instant {
        self.progress.start.checked_add(self.bounds.absolute).unwrap_or(self.progress.start)
    }

    /// Refresh the CPU signal. Kept off `poll` because the portable waiter
    /// polls every 10ms and a sample must never be that frequent; the rate
    /// limit lives in `CompilerCpuLiveness`, so calling this on every wake is
    /// correct at any wake rate.
    fn observe_cpu(&self) {
        self.cpu.observe(self.progress.start.elapsed());
    }

    /// `Ok(remaining)` is how long the process may stay exactly as it is
    /// before the nearest bound expires; `Err(detail)` means one already has.
    fn poll(&self) -> Result<Duration, CompilerTimeoutDetail> {
        let elapsed = self.progress.start.elapsed();
        let cpu = self.cpu.evidence(elapsed);
        let phase = self.retained_phase.lock().map(|phase| *phase);
        let fixed_deadline = match phase {
            Ok(RetainedProcessPhase::Compiling) => None,
            Ok(RetainedProcessPhase::Qualifying) => Some(self.bounds.absolute),
            Ok(RetainedProcessPhase::Executing { absolute_deadline }) => Some(absolute_deadline),
            Err(_) => Some(Duration::ZERO),
        };
        if let Some(deadline) = fixed_deadline {
            if elapsed >= deadline {
                return Err(CompilerTimeoutDetail {
                    bound: CompilerTimeoutBound::Absolute,
                    limit: deadline,
                    elapsed,
                    idle: elapsed.saturating_sub(self.progress.last_progress().unwrap_or_default()),
                    idle_limit: self.bounds.idle,
                    cpu,
                });
            }
            // A paused compiler is expected to be silent while its parent
            // qualifies finite evidence. Runtime output is untrusted. Both
            // phases retain this same watcher and its absolute deadline.
            return Ok((deadline - elapsed).min(self.cpu.interval));
        }
        let (idle, limit, bound) = match self.progress.last_progress() {
            Some(last) => {
                (elapsed.saturating_sub(last), self.bounds.idle, CompilerTimeoutBound::Idle)
            }
            // No byte has ever arrived: the whole run is one silent interval.
            None => (elapsed, self.bounds.silent, CompilerTimeoutBound::Silent),
        };
        // Quiet is not the same as stopped. The idle bound is the one that
        // fires on a compiler that has gone quiet, so it is armed only while
        // BOTH liveness signals are stale: no byte drained AND no CPU
        // consumed. `Unsampled` contributes nothing, so a platform (or a run)
        // without a reading keeps the output-only behaviour exactly.
        //
        // The silent regime deliberately does NOT consult CPU. It caps a
        // process that has never said anything at all, and letting CPU extend
        // that from 2h to the 8h ceiling is a different change from this one.
        let stalled = match (bound, cpu) {
            (CompilerTimeoutBound::Idle, CompilerCpuEvidence::Sampled { since_advance, .. }) => {
                idle.min(since_advance)
            }
            _ => idle,
        };
        // The stall bounds are checked first: when several expire together
        // (a flat configuration, say) the useful thing to report is that the
        // compiler stopped progressing, not that the clock ran out. The
        // absolute bound is therefore only ever reported when it is genuinely
        // the binding one -- a process that never went idle.
        if stalled >= limit {
            return Err(CompilerTimeoutDetail {
                bound,
                limit,
                elapsed,
                idle,
                idle_limit: self.bounds.idle,
                cpu,
            });
        }
        if elapsed >= self.bounds.absolute {
            return Err(CompilerTimeoutDetail {
                bound: CompilerTimeoutBound::Absolute,
                limit: self.bounds.absolute,
                elapsed,
                idle,
                idle_limit: self.bounds.idle,
                cpu,
            });
        }
        // The first drained byte switches the regime from `silent` to the far
        // shorter `idle`, which can move the deadline backwards. A caller that
        // slept on the silent bound would miss that, so never hand out an
        // interval longer than the shortest bound a regime change can impose.
        // The CPU interval joins that list for the same reason in reverse: a
        // caller that slept past it would never take the sample that the idle
        // bound now depends on.
        let regime_change = self.bounds.idle.min(self.bounds.silent);
        Ok((limit - stalled)
            .min(self.bounds.absolute - elapsed)
            .min(regime_change)
            .min(self.cpu.interval))
    }

    fn expire(&self, detail: CompilerTimeoutDetail) {
        if let Ok(mut slot) = self.detail.lock() {
            *slot = Some(detail);
        }
        // Published after the detail so any reader that sees the flag also
        // sees the reason.
        self.timed_out.store(true, Ordering::Release);
    }

    fn timed_out(&self) -> bool {
        self.timed_out.load(Ordering::Acquire)
    }

    fn timeout_message(&self) -> String {
        match self.detail.lock().ok().and_then(|slot| *slot) {
            Some(detail) => detail.message(),
            None => format!(
                "compiler process exceeded its bounds (silent {} / idle {} / absolute {}); \
                 the recorded reason was lost",
                format_bound_duration(self.bounds.silent),
                format_bound_duration(self.bounds.idle),
                format_bound_duration(self.bounds.absolute)
            ),
        }
    }
}

struct CompilerProcessGuard {
    #[cfg(unix)]
    cancel: Option<mpsc::Sender<()>>,
    #[cfg(unix)]
    watcher: Option<thread::JoinHandle<()>>,
    state: Arc<CompilerTimeoutState>,
    /// The compiler is owned while it is guarded: a signal to targo-trust, or
    /// targo-trust's death, stops it through the one stop path.
    _ownership: Ownership,
}

impl CompilerProcessGuard {
    fn configure(command: &mut Command) {
        crate::process_lifecycle::configure_own_group(command);
    }

    fn start(pid: u32, bounds: CompilerProcessBounds) -> Self {
        let ownership = Ownership::of(pid);
        let state = Arc::new(CompilerTimeoutState::new(pid, bounds));
        #[cfg(unix)]
        {
            let (sender, receiver) = mpsc::channel();
            let state_for_thread = Arc::clone(&state);
            // The channel still carries exactly one message -- cancellation --
            // so the watchdog cannot be kept alive by a lying producer. What
            // changed is the deadline it waits on: it is recomputed from the
            // drains' progress clock on every wake, so a compiler that is
            // still emitting keeps buying idle intervals (up to the absolute
            // bound) while one that has gone quiet buys nothing.
            let watcher = thread::spawn(move || {
                loop {
                    // Sampled before the poll that reads it, and rate-limited
                    // inside, so the wake rate sets an upper bound on the
                    // sample rate and never the other way round.
                    state_for_thread.observe_cpu();
                    let remaining = match state_for_thread.poll() {
                        Ok(remaining) => remaining.max(Duration::from_millis(1)),
                        Err(detail) => {
                            state_for_thread.expire(detail);
                            // The tree, not just the group: the compilers this
                            // driver spawned are not in its group, and stopping
                            // the driver alone orphans them onto pid 1 where
                            // nothing will ever stop them.
                            let _ = crate::process_lifecycle::stop_tree(pid, StopCause::Backstop);
                            return;
                        }
                    };
                    match receiver.recv_timeout(remaining) {
                        Err(RecvTimeoutError::Timeout) => continue,
                        Ok(()) | Err(RecvTimeoutError::Disconnected) => return,
                    }
                }
            });
            Self { cancel: Some(sender), watcher: Some(watcher), state, _ownership: ownership }
        }
        #[cfg(not(unix))]
        {
            Self { state, _ownership: ownership }
        }
    }

    /// Handed to every pipe drain so each byte it reads refreshes the idle
    /// clock. A drain that reports nothing leaves the guard on its silent
    /// bound, which is the old flat behaviour.
    fn progress(&self) -> Arc<CompilerProgress> {
        Arc::clone(&self.state.progress)
    }

    fn finish(mut self) -> Result<(), String> {
        self.cancel_watcher();
        // A signal to targo-trust may be what ended this compiler: what it
        // streamed is no verdict, and the stop owns the exit (3).
        crate::process_lifecycle::signals::hold_if_interrupted();
        if self.state.timed_out() { Err(self.state.timeout_message()) } else { Ok(()) }
    }

    fn cancel_watcher(&mut self) {
        #[cfg(unix)]
        {
            if let Some(cancel) = self.cancel.take() {
                let _ = cancel.send(());
            }
            if let Some(watcher) = self.watcher.take() {
                let _ = watcher.join();
            }
        }
    }

    /// Called while the child may still be RUNNING -- the wait failed, or a
    /// pipe it should have exposed is missing -- so the tree is still
    /// walkable and must be walked, for the same reason the watchdog's stop
    /// walks it (`Child::kill` where there are no process groups). The caller
    /// reaps the child afterwards.
    fn abort_before_reap(&mut self, child: &mut std::process::Child) {
        self.cancel_watcher();
        let _ = crate::process_lifecycle::stop_child(child, StopCause::Error);
    }
}

impl Drop for CompilerProcessGuard {
    fn drop(&mut self) {
        self.cancel_watcher();
    }
}

/// A verified compiler process one of its backstop's bounds ended
/// ([`CompilerProcessBounds::from_backstop`]) did not finish, so the run could
/// not run (plan §2): say so, name the knob that sets the bounds, and exit 3.
/// It never produced a verdict, and whatever rows it streamed before the kill
/// are not published as one.
fn backstop_ended_the_compiler(
    timeout: &str,
    backstop: trust_types::determinism::Backstop,
) -> ExitCode {
    let bounds = CompilerProcessBounds::from_backstop(backstop);
    // What the stop path did to the compiler's tree, from its record.
    let stopped = crate::process_lifecycle::recorded_stops()
        .into_iter()
        .rev()
        .find(|record| record.cause == StopCause::Backstop)
        .map(|record| {
            let mut text =
                format!("; the stop sent SIGTERM to {} process(es)", record.outcome.terminated);
            if let Some(words) = record.outcome.kill_words(None) {
                text.push_str(" and ");
                text.push_str(&words);
            }
            text
        })
        .unwrap_or_default();
    eprintln!(
        "targo trust: COULD NOT RUN: {timeout}{stopped}. The run's wall-clock backstop ended the \
         compiler (`[trust] backstop` = {} per mille, which bounds each verified compiler process \
         to {} silent, {} idle and {} absolute, never less than at 1000), so it has no verdict; a \
         run that legitimately needs longer raises `backstop` in the workspace root's [trust] \
         table",
        backstop.per_mille,
        format_bound_duration(bounds.silent),
        format_bound_duration(bounds.idle),
        format_bound_duration(bounds.absolute),
    );
    ExitCode::from(crate::determinism_report::EXIT_COULD_NOT_RUN)
}

fn wait_for_compiler_process(
    child: &mut std::process::Child,
    guard: &mut CompilerProcessGuard,
) -> std::io::Result<ExitStatus> {
    #[cfg(unix)]
    {
        let pid = child.id();
        loop {
            let exited = match crate::bounded_process::exited_without_reaping(child) {
                Ok(exited) => exited,
                Err(error) => {
                    guard.abort_before_reap(child);
                    return Err(error);
                }
            };
            if exited {
                // The unreaped leader reserves this PID as the group's PGID,
                // so stopping the group here cannot race PID reuse.
                //
                // In effect the GROUP and not the tree: the leader has already
                // exited, so its children were reparented to init the moment
                // it did and a walk from this pid finds nothing under the
                // unreaped leader. What can still be here is a descendant that
                // stayed in the leader's group, and the stop path's group
                // signal is exactly what reaches that.
                guard.cancel_watcher();
                let _ = crate::process_lifecycle::stop_tree(pid, StopCause::LeaderExited);
                return child.wait();
            }
            thread::sleep(Duration::from_millis(10));
        }
    }
    #[cfg(not(unix))]
    {
        // `std::process` can bound and reap the leader portably, but it cannot
        // contain arbitrary descendants. Windows job-object integration (or
        // the corresponding facility on another non-Unix target) is required
        // before this branch can make the Unix process-group guarantee.
        wait_for_compiler_leader_until(child, &guard.state)
    }
}

#[cfg(any(not(unix), test))]
fn wait_for_compiler_leader_until(
    child: &mut std::process::Child,
    state: &CompilerTimeoutState,
) -> std::io::Result<ExitStatus> {
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) => {
                state.observe_cpu();
                match state.poll() {
                    Err(detail) => {
                        state.expire(detail);
                        // The leader may exit between `try_wait` and the stop;
                        // waiting unconditionally both resolves that race and
                        // guarantees reap.
                        let _ = crate::process_lifecycle::stop_child(child, StopCause::Backstop);
                        return child.wait();
                    }
                    Ok(remaining) => thread::sleep(remaining.min(Duration::from_millis(10))),
                }
            }
            Err(error) => {
                let _ = crate::process_lifecycle::stop_child(child, StopCause::Error);
                let _ = child.wait();
                return Err(error);
            }
        }
    }
}

/// What the read side can say about the PIPE, as opposed to about the parser in
/// front of it.
///
/// `read(2)` on a pipe returns 0 exactly when the buffer is drained AND no
/// process holds a write end: that is the containment property, and it is the
/// only thing here that observes it directly. Everything after EOF -- however
/// long the parse takes -- happens with the pipe already closed, and therefore
/// says nothing about containment.
///
/// The two counters separate "blocked in `read(2)` on a pipe someone still
/// holds open" from "not in `read(2)` at all", so a diagnostic can state which
/// one it measured instead of asserting the first and hoping.
struct PipeReadState {
    /// Set once, by the reading thread, the first time the pipe reports EOF.
    eof: std::sync::OnceLock<Instant>,
    /// `read(2)` calls entered and returned. `started - completed` is the
    /// number outstanding, which for a single-threaded reader is 0 or 1.
    reads_started: AtomicU64,
    reads_completed: AtomicU64,
}

impl PipeReadState {
    fn new() -> Self {
        Self {
            eof: std::sync::OnceLock::new(),
            reads_started: AtomicU64::new(0),
            reads_completed: AtomicU64::new(0),
        }
    }

    fn eof_at(&self) -> Option<Instant> {
        self.eof.get().copied()
    }

    /// `(entered, returned)` as one observation.
    ///
    /// `started` is read FIRST on purpose. The two loads are not atomic
    /// together, so a reader that cycles between them can make the pair look
    /// like no read is outstanding when one is. That is the direction to err
    /// in: the diagnostic then says the pipe's state was not observed, instead
    /// of asserting a blocked read it did not see.
    fn read_counts(&self) -> (u64, u64) {
        let started = self.reads_started.load(Ordering::Acquire);
        let completed = self.reads_completed.load(Ordering::Acquire);
        (started, completed)
    }
}

/// A read side that reports every byte it delivers to the timeout guard, and
/// reports the pipe's own end-of-file to the close guard.
/// Wrapping the raw pipe rather than instrumenting the parsers keeps progress
/// independent of which parser is in front of it: the Cargo JSON stream, the
/// TRUSTJSON transport, and plain rendered diagnostics all count, and a parser
/// that buffers or discards a line cannot silently withhold liveness. EOF is
/// observed in the same place and for the same reason: a parser that is slow,
/// or that stops reading early, cannot move when the pipe closed.
struct ProgressReader<R> {
    inner: R,
    progress: Arc<CompilerProgress>,
    pipe: Arc<PipeReadState>,
}

impl<R: Read> Read for ProgressReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        // `read` into an EMPTY buffer returns `Ok(0)` without touching the
        // pipe, so it is not EOF and must not be recorded as one. `BufReader`
        // never does this, but the type does not stop a future caller from it.
        if buf.is_empty() {
            return Ok(0);
        }
        self.pipe.reads_started.fetch_add(1, Ordering::Release);
        let read = self.inner.read(buf);
        self.pipe.reads_completed.fetch_add(1, Ordering::Release);
        let read = read?;
        if read > 0 {
            self.progress.record();
        } else {
            // A pipe reports 0 only with every write end closed. Record when,
            // and keep the FIRST observation: a reader that keeps polling a
            // closed pipe must not push the timestamp forward.
            let _ = self.pipe.eof.set(Instant::now());
        }
        Ok(read)
    }
}

/// A parser thread's result, plus the pipe-lifetime facts its reader observed.
///
/// These travel together because the close guard needs both: the result says
/// the parse is done, and only the pipe state says whether the thing the guard
/// exists to catch -- a write end still held open -- is happening.
struct CompilerOutputChannel<T> {
    receiver: mpsc::Receiver<Result<T, String>>,
    pipe: Arc<PipeReadState>,
}

/// Run `parse` over `source` on its own thread, with the pipe wrapped so both
/// liveness and end-of-file are observed underneath whatever the parser does.
fn spawn_pipe_parser<R, T, F>(
    source: R,
    progress: Arc<CompilerProgress>,
    parse: F,
) -> CompilerOutputChannel<T>
where
    R: Read + Send + 'static,
    T: Send + 'static,
    F: FnOnce(ProgressReader<R>) -> Result<T, String> + Send + 'static,
{
    let (sender, receiver) = mpsc::sync_channel(1);
    let pipe = Arc::new(PipeReadState::new());
    let reader_pipe = Arc::clone(&pipe);
    thread::spawn(move || {
        let reader = ProgressReader { inner: source, progress, pipe: reader_pipe };
        let _ = sender.send(parse(reader));
    });
    CompilerOutputChannel { receiver, pipe }
}

fn spawn_compiler_stderr_parser(
    stderr: std::process::ChildStderr,
    progress: Arc<CompilerProgress>,
    crate_mode: bool,
    echo: bool,
    supports_json_transport: bool,
    expected_session: String,
    strict_artifact_policy: bool,
) -> CompilerOutputChannel<ParsedCompilerOutput> {
    spawn_pipe_parser(stderr, progress, move |stderr| {
        if crate_mode {
            let mut parsed = ParsedCompilerOutput::default();
            parsed.compiler_diagnostics =
                parse_untrusted_cargo_stderr(BufReader::new(stderr), echo);
            Ok(parsed)
        } else {
            parse_compiler_stderr(BufReader::new(stderr), echo)
                .require_structured_json_transport(supports_json_transport)
                .require_raw_coverage_authentication(&expected_session, strict_artifact_policy)
        }
    })
}

fn spawn_cargo_stdout_parser(
    stdout: std::process::ChildStdout,
    progress: Arc<CompilerProgress>,
    selected: BTreeMap<String, String>,
    expected_session: String,
    require_authenticated_coverage: bool,
    cargo_execution_mode: bool,
    prepared_tests: bool,
) -> CompilerOutputChannel<CargoCompilerEvidence> {
    spawn_pipe_parser(stdout, progress, move |stdout| {
        // `targo trust test` and `targo trust bench` compile execution
        // harnesses, then multiplex their untrusted stdout after Cargo's
        // authenticated build-finished boundary. The execution-mode parser
        // accepts that suffix without ever feeding it back into proof parsing.
        // Ordinary check/build keeps the strict all-JSON parser.
        if prepared_tests {
            parse_cargo_json_stdout_for_prepared_tests(
                BufReader::new(stdout),
                &selected,
                &expected_session,
                require_authenticated_coverage,
            )
        } else if cargo_execution_mode {
            parse_cargo_json_stdout_for_test(
                BufReader::new(stdout),
                &selected,
                &expected_session,
                require_authenticated_coverage,
            )
        } else {
            parse_cargo_json_stdout(
                BufReader::new(stdout),
                &selected,
                &expected_session,
                require_authenticated_coverage,
            )
        }
    })
}

/// Wait for a parser thread's result, bounding ONLY the thing the bound is
/// about: how long the evidence pipe may stay open after the compiler leader
/// exited.
///
/// Measured on ay 0.27.0's release gate, 2026-09-18: 323 units compiled with
/// zero failures over 359m, Cargo printed `Finished`, and 39s later the run was
/// discarded because this wait had expired -- while the Cargo stdout parser was
/// doing its post-EOF work, which for that stream is
/// `parse_cargo_json_stdout_impl`'s re-parse of ~150k retained TRUST_JSON
/// transport lines (`transport.rs`, the `for (target, lines) in transport_lines`
/// loop). Six hours of verification were thrown away by a timer that was never
/// measuring a containment property at all. A parse that runs long after EOF is
/// a big build, not an escaped process, and it now cannot fail a run.
///
/// The bound still exists, and still fails closed, but it is now applied to
/// end-of-file, which is the property the message names: `read(2)` on a pipe
/// returns 0 exactly when the buffer is drained and NO process holds a write
/// end. Once that is observed, containment is discharged as a fact and the
/// remaining wait is unbounded -- see the argument at the `recv` below.
fn receive_compiler_output<T>(
    channel: CompilerOutputChannel<T>,
    channel_name: &str,
) -> Result<T, String> {
    receive_compiler_output_within(
        channel,
        channel_name,
        COMPILER_OUTPUT_CLOSE_TIMEOUT,
        POST_EOF_PARSE_LIVENESS_BOUND,
    )
}

/// How often the close wait re-checks the pipe's end-of-file flag.
///
/// The wait is otherwise a blocking `recv_timeout`, so this only costs a wakeup:
/// 1200 of them across the shipped 30s bound, each an atomic load. It also caps
/// how stale the "how long did the parse take after EOF" figure can be.
const COMPILER_OUTPUT_CLOSE_POLL_INTERVAL: Duration = Duration::from_millis(25);

fn receive_compiler_output_within<T>(
    channel: CompilerOutputChannel<T>,
    channel_name: &str,
    close_timeout: Duration,
    post_eof_liveness_bound: Duration,
) -> Result<T, String> {
    let CompilerOutputChannel { receiver, pipe } = channel;
    let started = Instant::now();
    let deadline = started.checked_add(close_timeout).unwrap_or(started);
    // The read counters as the wait begins, so the diagnostic can say whether
    // the pipe delivered anything DURING the window rather than only whether a
    // read is outstanding at the end of it.
    let opening = pipe.read_counts();
    loop {
        if let Some(eof_at) = pipe.eof_at() {
            // The pipe is closed. Nothing that happens from here can be a
            // containment failure, and the wait is unbounded on purpose:
            //
            // * the input is finite and already fully read, and the parsers cap
            //   it (`MAX_CARGO_JSON_LINE_BYTES`, the aggregate transport
            //   ceiling), so the remaining work is bounded;
            // * it is pure CPU over memory -- no I/O, no locks, and the one
            //   `eprint!` path belongs to the read loop, not to what follows
            //   EOF;
            // * a parser that panics drops its sender, so `recv` returns
            //   `Disconnected` rather than blocking. The only way to hang here
            //   is a parser that neither returns nor unwinds, which is a bug in
            //   this crate's own code and is not what a containment timer is
            //   for.
            //
            // Putting a CONTAINMENT-sized number here instead would re-create
            // exactly the defect above: a bound on parse time, wearing the
            // words of a bound on process containment.
            //
            // A LIVENESS backstop is a different claim, and it is kept. After
            // EOF nothing else in this process bounds the run --
            // `process_guard.finish()` has already returned -- so a parser that
            // neither returns nor unwinds would hang a release gate silently
            // and forever, which is strictly worse than the failure this commit
            // removes. `POST_EOF_PARSE_LIVENESS_BOUND` is deliberately far
            // above any parse a run can produce, and its message says plainly
            // that it is a bug in this crate rather than a containment finding,
            // so it can never be read as evidence about an uncontained writer.
            return match receiver.recv_timeout(post_eof_liveness_bound) {
                Ok(result) => {
                    let parsing = eof_at.elapsed();
                    if parsing >= close_timeout {
                        // This run would have been discarded before this guard
                        // measured EOF. Say so, with the numbers, so the next
                        // build this size is a known quantity and not an
                        // incident.
                        let closed = if eof_at <= started {
                            "was already closed when this wait began".to_string()
                        } else {
                            format!(
                                "closed {:?} into this wait",
                                eof_at.saturating_duration_since(started)
                            )
                        };
                        eprintln!(
                            "targo trust: note: {channel_name} {closed}, and its parser then took {parsing:?} more to finish; the pipe was shut for all of it, so this is stream size, not containment"
                        );
                    }
                    result
                }
                Err(RecvTimeoutError::Disconnected) => {
                    Err(format!("{channel_name} parser terminated without returning a result"))
                }
                Err(RecvTimeoutError::Timeout) => Err(format!(
                    "{channel_name} reached end-of-file {eof:?} after the compiler leader exited, \
                     but its parser has still not finished {bound:?} later. The pipe is CLOSED, \
                     so this is NOT a containment finding and says nothing about any descendant \
                     of this process; it is a liveness bug in this crate's own parser for this \
                     input. Report it with the size of the build that produced it.",
                    eof = eof_at.saturating_duration_since(started),
                    bound = post_eof_liveness_bound,
                )),
            };
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            // A parser can also return early -- a malformed line is an `Err`
            // long before EOF -- so a result that is already waiting outranks
            // the timeout.
            match receiver.try_recv() {
                Ok(result) => return result,
                Err(mpsc::TryRecvError::Disconnected) => {
                    return Err(format!(
                        "{channel_name} parser terminated without returning a result"
                    ));
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            if pipe.eof_at().is_some() {
                // EOF landed inside this branch; the top of the loop owns it.
                continue;
            }
            return Err(pipe_not_closed_error(channel_name, close_timeout, &pipe, opening));
        }
        match receiver.recv_timeout(remaining.min(COMPILER_OUTPUT_CLOSE_POLL_INTERVAL)) {
            Ok(result) => return result,
            Err(RecvTimeoutError::Timeout) => {}
            Err(RecvTimeoutError::Disconnected) => {
                return Err(format!("{channel_name} parser terminated without returning a result"));
            }
        }
    }
}

/// The close guard's refusal, stating what was measured and naming who could be
/// responsible.
///
/// "An uncontained descendant MAY still own the pipe" is the shape of
/// diagnostic this project keeps having to re-investigate months later: it
/// asserts a cause it never observed and names nobody, so it can neither be
/// confirmed nor refuted from the log. This says which of the three
/// distinguishable states the reader was actually in, and lists the processes
/// still descending from this one with their argv.
fn pipe_not_closed_error(
    channel_name: &str,
    close_timeout: Duration,
    pipe: &PipeReadState,
    opening: (u64, u64),
) -> String {
    let (entered, returned) = pipe.read_counts();
    let outstanding = entered.saturating_sub(returned);
    let delivered = returned.saturating_sub(opening.1);
    // Only one of these three is a statement about the PIPE. Say which one was
    // measured, so a reader of the log can tell a containment failure from a
    // consumer that stopped asking.
    let observation = if outstanding > 0 && delivered == 0 {
        "the read side has been blocked inside read(2) on that pipe for the whole window, delivering nothing, and a pipe blocks a reader only while some process holds a write end open"
            .to_string()
    } else if outstanding > 0 {
        format!(
            "the read side is blocked inside read(2) on that pipe, after {delivered} further read(2) result(s) during the window, and a pipe blocks a reader only while some process holds a write end open"
        )
    } else {
        format!(
            "the read side is NOT inside read(2) -- it is between reads after {delivered} result(s) during the window -- so the pipe's state is unobserved here rather than known to be open, and the stall is in this process's own parser"
        )
    };
    format!(
        "{channel_name} did not reach end-of-file within {close_timeout:?} of the compiler leader exiting; {observation}; {}",
        render_surviving_descendants(&surviving_descendants())
    )
}

// ---------------------------------------------------------------------------
// Utility functions (used by pipeline and main)
// ---------------------------------------------------------------------------

pub(crate) fn has_output_path_flag(args: &[String]) -> bool {
    args.iter().any(|arg| {
        arg == "-o"
            || (arg.starts_with("-o") && arg.len() > 2)
            || arg == "--out-dir"
            || arg.starts_with("--out-dir=")
    })
}

/// Proof transport requires Cargo's plain `json` format. Trust evidence rides
/// rustc NOTE diagnostics (`TRUST_JSON:...`), and only plain JSON preserves
/// those diagnostics inside authenticated Cargo `compiler-message` envelopes.
/// `json-render-diagnostics` renders them directly to stderr, losing the
/// `trust_compile_target` identity that the parser intentionally requires.
/// Human-readable diagnostics are retained because the parser re-emits every
/// non-transport message's rendered text.
fn cargo_args_without_message_format(args: &[String]) -> Result<Vec<String>, String> {
    let mut output = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--" {
            output.extend(args[index..].iter().cloned());
            return Ok(output);
        }
        if arg == "--message-format" {
            index += 1;
            if args.get(index).is_none_or(|value| value.is_empty() || value.starts_with('-')) {
                return Err("--message-format requires a value".to_string());
            }
        } else if arg.starts_with("--message-format=") {
            if arg == "--message-format=" {
                return Err("--message-format requires a value".to_string());
            }
        } else {
            output.push(arg.clone());
        }
        index += 1;
    }
    Ok(output)
}

fn insert_cargo_arg_before_passthrough(args: &mut Vec<String>, arg: impl Into<String>) {
    let index = args.iter().position(|candidate| candidate == "--").unwrap_or(args.len());
    args.insert(index, arg.into());
}

fn cargo_args_with_proof_message_format(args: &[String]) -> Result<Vec<String>, String> {
    let mut output = cargo_args_without_message_format(args)?;
    insert_cargo_arg_before_passthrough(&mut output, "--message-format=json");
    Ok(output)
}

fn cargo_arg_before_passthrough(args: &[String], predicate: impl Fn(&str) -> bool) -> bool {
    args.iter().take_while(|arg| arg.as_str() != "--").any(|arg| predicate(arg))
}

fn cargo_test_has_explicit_target_selector(args: &[String]) -> bool {
    cargo_arg_before_passthrough(args.get(1..).unwrap_or_default(), |arg| {
        matches!(arg, "--lib" | "--bins" | "--examples" | "--tests" | "--benches" | "--all-targets")
            || ["--bin=", "--example=", "--test=", "--bench="]
                .iter()
                .any(|prefix| arg.starts_with(prefix))
            || matches!(arg, "--bin" | "--example" | "--test" | "--bench")
    })
}

/// Validate the currently supported evidence-grade Cargo test surface and
/// remove caller-selected message formats. Cargo does not precompile doctests
/// under `--no-run`; until rustdoc exposes an authenticated reusable
/// executable lane, explicit doctest-only requests fail closed.
fn cargo_test_non_doc_args(args: &[String]) -> Result<Vec<String>, String> {
    if !args.first().is_some_and(|arg| arg == "test") {
        return Err("internal error: Cargo test argument normalization received another command"
            .to_string());
    }
    if cargo_arg_before_passthrough(args, |arg| arg == "--doc") {
        return Err(
            "evidence-grade `targo trust test --doc` is unavailable: Cargo/rustdoc cannot precompile and authenticate reusable doctest executables"
                .to_string(),
        );
    }
    cargo_args_without_message_format(args)
}

fn cargo_test_compile_only_args(args: &[String]) -> Result<Vec<String>, String> {
    // Preserve Cargo's default non-doc compile filter, including examples it
    // compiles but does not execute. `--no-run` already prevents rustdoc's
    // separate doctest compile/execute lane.
    let mut output = cargo_test_non_doc_args(args)?;
    if !cargo_arg_before_passthrough(&output, |arg| arg == "--no-run") {
        insert_cargo_arg_before_passthrough(&mut output, "--no-run");
    }
    insert_cargo_arg_before_passthrough(&mut output, "--message-format=json");
    Ok(output)
}

fn cargo_test_retained_args(args: &[String]) -> Result<Vec<String>, String> {
    if cargo_arg_before_passthrough(args, |arg| arg == "--no-run") {
        return Err("a compile-only Cargo test request has no retained execution grant".to_string());
    }
    #[cfg(unix)]
    {
        let flag = trust_test_execution::retained::RETAINED_SESSION_ARG;
        if cargo_arg_before_passthrough(args, |arg| arg == flag) {
            return Err("the retained execution endpoint is owned by the verifier frontend".into());
        }
        let mut output = cargo_test_compile_only_args(args)?;
        insert_cargo_arg_before_passthrough(&mut output, flag);
        Ok(output)
    }
    #[cfg(not(unix))]
    {
        Err("retained verified tests require a Unix native companion".into())
    }
}

/// Authenticate the child Targo path against the selected compiler and use
/// that exact executable for Cargo metadata/package selection. Re-discovering
/// a frontend after command construction could bind coverage to one Targo and
/// execute another.
pub(super) fn resolve_cargo_selection_for_compiler(
    args: &[String],
    rustc_path: &Path,
    program: &str,
) -> Result<ResolvedCargoSelection, String> {
    let expected_targo = native_trust_cargo_path(rustc_path)?;
    let actual_targo = Path::new(program);
    let expected_identity = expected_targo.canonicalize().map_err(|error| {
        format!(
            "could not resolve selected compiler's sibling Targo `{}`: {error}",
            expected_targo.display()
        )
    })?;
    let actual_identity = actual_targo.canonicalize().map_err(|error| {
        format!("could not resolve invoked Targo `{}`: {error}", actual_targo.display())
    })?;
    if actual_identity != expected_identity {
        return Err(format!(
            "invoked Targo `{}` is not the authenticated sibling `{}` of selected compiler `{}`",
            actual_targo.display(),
            expected_targo.display(),
            rustc_path.display()
        ));
    }
    resolve_cargo_selection_with_targo(args, &expected_targo, rustc_path)
}

pub(super) fn single_file_report_subject(args: &[String]) -> Result<String, String> {
    let source = args
        .iter()
        .find(|argument| argument.ends_with(".rs") && !argument.starts_with('-'))
        .ok_or_else(|| {
            "single-file verification command omitted its Rust source path".to_string()
        })?;
    let canonical = Path::new(source).canonicalize().map_err(|error| {
        format!("could not canonicalize single-file report subject `{source}`: {error}")
    })?;
    canonical_single_file_report_subject(&canonical)
}

pub(super) fn canonical_single_file_report_subject(canonical: &Path) -> Result<String, String> {
    let canonical = canonical.to_str().ok_or_else(|| {
        format!("canonical single-file report subject is not valid UTF-8: {}", canonical.display())
    })?;
    Ok(format!("single-file(source={canonical:?})"))
}

fn temp_single_file_output_path(args: &[String]) -> PathBuf {
    let stem = args
        .iter()
        .find(|arg| arg.ends_with(".rs"))
        .and_then(|arg| Path::new(arg).file_stem())
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .unwrap_or("trust-check");
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let suffix = if cfg!(windows) { ".exe" } else { "" };
    let sequence = SINGLE_FILE_OUTPUT_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    env::temp_dir()
        .join(format!("targo-trust-single-{}-{nanos}-{sequence}", std::process::id()))
        .join(format!("{stem}{suffix}"))
}

static SINGLE_FILE_OUTPUT_SEQUENCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

struct EphemeralSingleFileOutput {
    directory: PathBuf,
}

impl Drop for EphemeralSingleFileOutput {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

fn prepare_ephemeral_single_file_output(
    args: &[String],
    enabled: bool,
) -> std::io::Result<Option<EphemeralSingleFileOutput>> {
    if !enabled {
        return Ok(None);
    }
    let output = args
        .windows(2)
        .rev()
        .find_map(|pair| (pair[0] == "-o").then(|| PathBuf::from(&pair[1])))
        .ok_or_else(|| std::io::Error::other("missing internal single-file output path"))?;
    let directory = output
        .parent()
        .ok_or_else(|| std::io::Error::other("internal single-file output has no parent"))?
        .to_path_buf();
    std::fs::create_dir(&directory)?;
    Ok(Some(EphemeralSingleFileOutput { directory }))
}

#[cfg(test)]
pub(crate) fn compiler_help_supports_option(help: &str, option: &str) -> bool {
    help.lines().any(|line| line.contains(option))
}

fn trust_verify_disable_option(z_value: &str) -> Option<&'static str> {
    let (_name, value) =
        z_value.split_once('=').map_or((z_value, None), |(name, value)| (name, Some(value)));

    match canonical_rustc_option_name(z_value).as_ref() {
        // Unlike the Boolean opt-outs below, either value (or even a malformed
        // value) is forbidden: the retired projection is not a Targo mode.
        "contract-checks" => Some("-Z contract-checks"),
        "trust-verify" if value == Some("off") => Some("-Z trust-verify=off"),
        "trust-verify" if rustc_bool_value(value) == Some(false) => Some("-Z trust-verify=false"),
        // The compiler still honours the retired `-Zno-trust-verify` alias (a
        // one-seed-generation bridge: bare or a true-ish value means
        // verification OFF, and it is rewritten to `trust-verify` before the
        // driver can tell the two apart), so an ambient alias is the same
        // off-switch under another name. `=off`/`=false` means verification
        // ON and is not a disable.
        "no-trust-verify" if rustc_bool_value(value) == Some(true) => Some("-Z no-trust-verify"),
        "trust-verify-full" if rustc_bool_value(value) == Some(false) => {
            Some("-Z trust-verify-full=false")
        }
        _ => None,
    }
}

fn rustc_bool_value(value: Option<&str>) -> Option<bool> {
    match value {
        None | Some("y") | Some("yes") | Some("on") | Some("true") => Some(true),
        Some("n") | Some("no") | Some("off") | Some("false") => Some(false),
        _ => None,
    }
}

pub(crate) fn find_trust_verify_disable_arg(args: &[String]) -> Option<String> {
    for (idx, arg) in args.iter().enumerate() {
        if arg == "-Z" {
            if let Some(next) = args.get(idx + 1).and_then(|next| trust_verify_disable_option(next))
            {
                return Some(next.to_string());
            }
            continue;
        }

        if let Some(option) = arg.strip_prefix("-Z").filter(|option| !option.is_empty()) {
            if let Some(disabled) = trust_verify_disable_option(option) {
                return Some(disabled.to_string());
            }
        }
    }

    None
}

fn find_retired_contract_checks_arg(args: &[String]) -> Option<String> {
    for (idx, arg) in args.iter().enumerate() {
        let option = if arg == "-Z" {
            args.get(idx + 1).map(String::as_str)
        } else {
            arg.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "contract-checks") {
            return Some("-Z contract-checks".to_string());
        }
    }
    None
}

fn find_targo_policy_override_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        if argument == "-Z" {
            if let Some(option) = args.get(index + 1) {
                if targo_owned_z_option(option, true) {
                    return Some(format!("-Z {option}"));
                }
            }
            index += 2;
            continue;
        }
        if let Some(option) = argument.strip_prefix("-Z").filter(|option| !option.is_empty()) {
            if targo_owned_z_option(option, true) {
                return Some(format!("-Z {option}"));
            }
        }
        index += 1;
    }
    None
}

fn find_forbidden_in_process_z_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "llvm-plugins") {
            return Some(if argument == "-Z" {
                format!("-Z {}", option.expect("matched split option"))
            } else {
                argument.clone()
            });
        }
        index += if argument == "-Z" { 2 } else { 1 };
    }
    None
}

fn dep_info_only_emit_spec(spec: &str) -> bool {
    let mut kinds = spec.split(',').filter(|kind| !kind.is_empty()).peekable();
    kinds.peek().is_some()
        && kinds.all(|kind| kind.split_once('=').map_or(kind, |(name, _)| name) == "dep-info")
}

fn find_direct_compiler_early_exit_arg(args: &[String]) -> Option<String> {
    if let Some(help) = find_codegen_help_arg(args) {
        return Some(help);
    }
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        if matches!(argument.as_str(), "-h" | "--help" | "-V" | "-vV" | "--version")
            || argument == "--explain"
            || argument.starts_with("--explain=")
            || argument == "--print"
            || argument.starts_with("--print=")
            || argument == "--pretty"
            || argument.starts_with("--pretty=")
        {
            return Some(argument.clone());
        }
        if argument == "--emit" {
            if let Some(spec) = args.get(index + 1) {
                if dep_info_only_emit_spec(spec) {
                    return Some(format!("--emit {spec}"));
                }
            }
            index += 2;
            continue;
        }
        if let Some(spec) = argument.strip_prefix("--emit=") {
            if dep_info_only_emit_spec(spec) {
                return Some(argument.clone());
            }
        }

        let z_option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if let Some(option) = z_option {
            let name = canonical_rustc_option_name(option);
            // Only the `mir-only` sink truncates the compile before evidence; the
            // other `-Ztrust-dump` sinks publish alongside a normal run.
            let dump_stops_the_compile = name == "trust-dump"
                && option.split_once('=').is_some_and(|(_, value)| value.starts_with("mir-only:"));
            if dump_stops_the_compile
                || matches!(
                    name.as_ref(),
                    "help"
                        | "link-only"
                        | "ls"
                        | "no-analysis"
                        | "parse-crate-root-only"
                        | "unpretty"
                )
            {
                return Some(format!("-Z {option}"));
            }
        }
        let lint_option = if matches!(argument.as_str(), "-W" | "-A" | "-D" | "-F") {
            args.get(index + 1).map(String::as_str)
        } else {
            argument
                .get(..2)
                .filter(|prefix| matches!(*prefix, "-W" | "-A" | "-D" | "-F"))
                .and_then(|_| argument.get(2..))
                .filter(|option| !option.is_empty())
        };
        if lint_option == Some("help") {
            return Some(argument.clone());
        }
        index += if matches!(argument.as_str(), "-Z" | "-W" | "-A" | "-D" | "-F") { 2 } else { 1 };
    }
    None
}

/// Reject compiler argument constructs whose effective token stream is not the
/// one inspected by targo-trust. rustc expands every `@path` argument before
/// parsing options (including `@shell:path` when shell argfiles are enabled),
/// while `--` changes the meaning of every argument that follows it. A direct
/// evidence-grade invocation must therefore use an explicit, inspectable argv;
/// otherwise an argfile can hide a policy override or a separator can strand
/// canonical safety flags outside the option parser.
fn validate_direct_rustc_passthrough(args: &[String]) -> Result<(), String> {
    if let Some(argfile) = args.iter().find(|argument| argument.starts_with('@')) {
        return Err(format!(
            "direct evidence-grade compiler arguments cannot contain response or shell argfiles (`{argfile}`); pass each rustc argument explicitly"
        ));
    }
    if args.iter().any(|argument| argument == "--") {
        return Err(
            "direct evidence-grade compiler arguments cannot contain a semantic `--` separator; pass the Rust source and each rustc option explicitly"
                .to_string(),
        );
    }
    if let Some(flag) = find_forbidden_in_process_z_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` loads plugin code inside trustc; in-process extension channels are forbidden"
        ));
    }
    if direct_rustc_uses_retired_valtree_node_limit(args) {
        return Err(
            "direct evidence-grade compiler arguments use retired `-Zvaltree-node-limit`; verified compilations enforce rustc's fixed valtree resource limit"
                .to_string(),
        );
    }
    if let Some(flag) = find_forbidden_in_process_codegen_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` can load LLVM plugin code inside trustc; in-process extension channels are forbidden"
        ));
    }
    if let Some(flag) = find_direct_compiler_early_exit_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` exits before authenticated Trust coverage is closed"
        ));
    }
    if let Some(flag) = find_targo_policy_override_arg(args) {
        return Err(format!(
            "passthrough argument `{flag}` conflicts with targo-trust's verifier policy; use the corresponding public targo trust option"
        ));
    }
    if let Some(external) = args.iter().enumerate().find_map(|(index, argument)| {
        (argument == "--extern")
            .then(|| args.get(index + 1).cloned().unwrap_or_else(|| "<missing>".to_string()))
            .or_else(|| argument.strip_prefix("--extern=").map(str::to_string))
    }) {
        return Err(format!(
            "direct evidence-grade compiler arguments cannot authenticate whether --extern={external} loads an in-process proc macro capable of forging raw TRUSTJSON transport; use verified Cargo mode, which enforces the no-proc-macro TCB boundary"
        ));
    }
    Ok(())
}

fn direct_rustc_uses_retired_valtree_node_limit(args: &[String]) -> bool {
    args.iter().enumerate().any(|(index, argument)| {
        let z_option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        z_option.is_some_and(|option| canonical_rustc_option_name(option) == "valtree-node-limit")
    })
}

fn direct_rustc_target(args: &[String]) -> Result<Option<&str>, String> {
    let mut target = None;
    let mut target_count = 0usize;
    let mut index = 0usize;
    while index < args.len() {
        let candidate = if args[index] == "--target" {
            index += 1;
            Some(
                args.get(index)
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| "direct rustc --target requires a non-empty value".to_string())?
                    .as_str(),
            )
        } else {
            args[index]
                .strip_prefix("--target=")
                .map(|value| {
                    if value.is_empty() {
                        Err("direct rustc --target requires a non-empty value".to_string())
                    } else {
                        Ok(value)
                    }
                })
                .transpose()?
        };
        if let Some(candidate) = candidate {
            target_count += 1;
            if let Some(previous) = target {
                return Err(if previous == candidate {
                    format!(
                        "direct evidence-grade rustc received duplicate --target value `{candidate}`"
                    )
                } else {
                    format!(
                        "direct evidence-grade rustc received conflicting --target values `{previous}` and `{candidate}`"
                    )
                });
            }
            target = Some(candidate);
        }
        index += 1;
    }
    debug_assert_eq!(target_count, usize::from(target.is_some()));
    Ok(target)
}

fn validate_direct_custom_target_extension_tcb(target: &str) -> Result<(), String> {
    let target_path = Path::new(target);
    let mut candidates = Vec::new();
    if target.ends_with(".json") || target_path.components().count() > 1 {
        candidates.push(target_path.to_path_buf());
    } else if let Some(search_path) = env::var_os("RUST_TARGET_PATH") {
        candidates.extend(
            env::split_paths(&search_path)
                .map(|directory| directory.join(format!("{target}.json")))
                .filter(|path| path.exists()),
        );
    }

    for path in candidates {
        let bytes = crate::input_limits::read_bounded_file(
            &path,
            crate::input_limits::MAX_RELEASE_METADATA_BYTES,
        )
        .map_err(|error| {
            format!(
                "cannot inspect custom target `{}` before verification: {error}",
                path.display()
            )
        })?;
        let spec: serde_json::Value = serde_json::from_slice(&bytes).map_err(|error| {
            format!("cannot parse custom target `{}` before verification: {error}", path.display())
        })?;
        for key in ["llvm-args", "llvm_args"] {
            let Some(value) = spec.get(key) else { continue };
            let empty = value.as_array().is_some_and(Vec::is_empty) || value.is_null();
            if !empty {
                return Err(format!(
                    "direct evidence-grade compilation rejects non-empty custom-target `{key}` in `{}`: LLVM extension arguments execute inside trustc's proof-transport TCB",
                    path.display()
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn find_trust_verify_disable_in_rustflags(flags: &str) -> Option<String> {
    let args = flags
        .split(' ')
        .map(str::trim)
        .filter(|flag| !flag.is_empty())
        .map(str::to_string)
        .collect::<Vec<_>>();
    find_trust_verify_disable_arg(&args)
}

fn find_trust_verify_disable_in_encoded_rustflags(flags: &str) -> Option<String> {
    let args = flags.split('\x1f').map(str::to_string).collect::<Vec<_>>();
    find_trust_verify_disable_arg(&args)
}

pub(crate) fn trust_verify_disable_diagnostic(
    passthrough: &[String],
    rustc_passthrough: bool,
) -> Option<String> {
    if env::var_os("TRUST_VERIFY_FN_BUDGET_MS").is_some() {
        return Some(
            "TRUST_VERIFY_FN_BUDGET_MS is retired; the clocks follow `backstop` in the workspace root manifest's [trust] table"
                .to_string(),
        );
    }
    if rustc_passthrough {
        if let Some(flag) = find_trust_verify_disable_arg(passthrough) {
            return Some(format!("passthrough argument `{flag}` is not allowed"));
        }
        if let Some(flag) = find_targo_policy_override_arg(passthrough) {
            return Some(format!(
                "passthrough argument `{flag}` conflicts with targo-trust's verifier policy; \
                 use the corresponding public targo trust option"
            ));
        }
    }

    if let Ok(flags) = env::var("RUSTFLAGS") {
        if let Some(flag) = find_trust_verify_disable_in_rustflags(&flags) {
            return Some(format!("RUSTFLAGS contains `{flag}`"));
        }
    }

    if let Ok(flags) = env::var("CARGO_ENCODED_RUSTFLAGS") {
        if let Some(flag) = find_trust_verify_disable_in_encoded_rustflags(&flags) {
            return Some(format!("CARGO_ENCODED_RUSTFLAGS contains `{flag}`"));
        }
    }

    // `cargo test --doc` and future documentation-bearing verified commands
    // use Cargo's parallel rustdoc flag channels. rustdoc accepts rustc's
    // unstable session options, so the retired exec projection must be denied
    // there just as it is in the ordinary compiler flag stream.
    if let Ok(flags) = env::var("RUSTDOCFLAGS") {
        let args = flags
            .split(' ')
            .map(str::trim)
            .filter(|flag| !flag.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>();
        if let Some(flag) = find_retired_contract_checks_arg(&args) {
            return Some(format!("RUSTDOCFLAGS contains `{flag}`"));
        }
    }

    if let Ok(flags) = env::var("CARGO_ENCODED_RUSTDOCFLAGS") {
        let args = flags.split('\x1f').map(str::to_string).collect::<Vec<_>>();
        if let Some(flag) = find_retired_contract_checks_arg(&args) {
            return Some(format!("CARGO_ENCODED_RUSTDOCFLAGS contains `{flag}`"));
        }
    }

    None
}

/// The verified lane's complete flags, in the order the sibling Targo appends
/// them to the project's own: the lane's policy (`lane_rustflags`), then the
/// per-run verification controls (budgets, session, proof root, policy,
/// profile), then the adopted project requirements, merged last so a changed
/// requirement re-verifies affected units exactly like a policy change would.
fn verified_lane_flags(
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    requirements: &ProjectRequirementFlags,
) -> Result<Vec<String>, String> {
    let mut lane = lane_rustflags(
        &config.level,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
    );
    append_verification_control_args(&mut lane, controls)?;
    // Trust (D21): isolation is the sibling Targo's per-unit default, so the
    // lane says nothing unless this run switched it off.
    if !config.proc_macro_isolation {
        lane.extend(["-Z".to_string(), "trust-proc-macro-isolation=no".to_string()]);
    }
    requirements.apply_to_args(&mut lane);
    Ok(lane)
}

struct LaneFlagsInput<'a, 'policy> {
    cmd: &'a mut Command,
    config: &'a TrustConfig,
    selected_codegen_backend: Option<&'a str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &'a VerificationControls<'policy>,
    requirements: &'a ProjectRequirementFlags,
    cargo_args: &'a [String],
}

/// Hand the verified lane to the child Cargo (T14a, DECISION_QUEUE
/// T14-APPEND-1). The lane travels in `TRUST_TARGO_LANE_RUSTFLAGS`; the
/// caller's RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS are left as they are, and
/// the sibling Targo resolves the project's flags from them or from the
/// project's configuration by Cargo's own precedence, drops what the lane
/// owns, and appends the lane. A unit's flags are `<project> <lane>`, and
/// Cargo fingerprints both.
fn apply_lane_flags_env(input: LaneFlagsInput<'_, '_>) -> Result<(), String> {
    let LaneFlagsInput {
        cmd,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        requirements,
        cargo_args,
    } = input;
    // The sibling Targo drops an environment `-Ztrust-*` token silently (the
    // lane is the only Trust input); name where each per-run selection lives,
    // so an ignored ambient flag is visible instead of a mystery.
    if let Some(warning) = inherited_trust_rustflags_warning(
        env::var("CARGO_ENCODED_RUSTFLAGS").ok().as_deref(),
        env::var("RUSTFLAGS").ok().as_deref(),
    ) {
        eprintln!("targo trust: {warning}");
    }
    // The sibling Targo drops every project `-Zcodegen-backend`,
    // `-Zllvm-plugins` and `-Cllvm-args`, configured or inherited, with a
    // notice. When a channel carried a Kani surface (the trust-mc dylib,
    // `register_tool(kanitool)`), say so: a strict PASS must never silently
    // stand in for a Kani verdict (kani_gate premise 2).
    if let Some(disclosure) = super::kani_gate::inherited_kani_surface_disclosure(cargo_args) {
        eprintln!("targo trust: {disclosure}");
    }
    let lane = verified_lane_flags(
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        requirements,
    )?;
    cmd.env(TRUST_TARGO_LANE_RUSTFLAGS_ENV, encode_lane_rustflags(&lane)?);
    if selected_codegen_backend == Some("trust-cg") {
        // Cargo's profile-level incremental switch is independent of
        // rustflags. Disable it before Unit construction so no incremental
        // directory or reuse fingerprint is created for a backend that does
        // not implement incremental object reuse.
        cmd.env("CARGO_INCREMENTAL", "0");
    }
    Ok(())
}

/// The compiler's `-Ztrust-policy` domain, as selected by this run's lane.
///
/// Held as one value rather than a pair of booleans because the compiler
/// rejects the pair: emitting both `memory-safe` and `advisory` was a
/// representable state here that no compilation could accept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TrustPolicySelection {
    Strict,
    /// Release gate: `-Ztrust-policy=certify`, full static discharge.
    Certify,
    Advisory,
    MemorySafe,
}

impl TrustPolicySelection {
    /// Resolve the lane flags the CLI carries. Memory-safe is the narrow
    /// policy and advisory the broad one, so a run that somehow asked for both
    /// gets the narrower guarantee.
    pub(crate) fn from_lane_flags(memory_safe: bool, survey: bool, certify: bool) -> Self {
        // `certify` is the tightening lane and wins over nothing — the CLI
        // rejects combining it with a loosener — but it is checked first so the
        // resolution order reads tightest-to-loosest.
        if certify {
            Self::Certify
        } else if memory_safe {
            Self::MemorySafe
        } else if survey {
            Self::Advisory
        } else {
            Self::Strict
        }
    }

    /// `None` for the compiler's own default, so a strict run's command line
    /// stays free of a redundant tracked option.
    fn option_value(self) -> Option<&'static str> {
        match self {
            Self::Strict => None,
            Self::Certify => Some("certify"),
            Self::Advisory => Some("advisory"),
            Self::MemorySafe => Some("memory-safe"),
        }
    }
}

/// The `-Ztrust-policy` the CLI lane puts on the compile before the project
/// requirements are merged: the lane-flag selection, except that `--allow-l0-gaps` on the
/// strict selection is appended as `advisory` by the backend's mode flags.
fn lane_compiler_policy(
    memory_safe_policy: bool,
    survey: bool,
    certify_gate: bool,
    allow_l0_gaps: bool,
) -> &'static str {
    match TrustPolicySelection::from_lane_flags(memory_safe_policy, survey, certify_gate) {
        TrustPolicySelection::Strict if allow_l0_gaps => "advisory",
        selection => selection.option_value().unwrap_or("strict"),
    }
}

/// The adopted project requirements for this run's compile, refused before
/// any compiler runs when one disagrees with the lane, hardened profile or
/// level the run resolved ([`ProjectRequirementFlags::for_run`]).
fn requirement_flags_for_run(
    config: &TrustConfig,
    memory_safe_policy: bool,
    survey: bool,
    certify_gate: bool,
    allow_l0_gaps: bool,
    hardened_profile: Option<&str>,
) -> Result<ProjectRequirementFlags, String> {
    ProjectRequirementFlags::for_run(
        config.project_policy.as_ref(),
        lane_compiler_policy(memory_safe_policy, survey, certify_gate, allow_l0_gaps),
        hardened_profile,
        level_to_num(&config.level),
    )
}

#[derive(Clone, Copy)]
struct VerificationControls<'a> {
    policy: TrustPolicySelection,
    /// The run's budget profile: the one effort count's scale and the
    /// backstop the two compiler clocks are derived from (plan §3.6).
    budget: &'a trust_types::determinism::BudgetProfile,
    hardened_profile: Option<&'a str>,
    verification_session: &'a str,
    proof_artifact_root: &'a Path,
    /// Trust (v6/D1): directory for the compiler's kernel-graded Clean goal
    /// artifact (`targo trust spec --emit clean`). Deliberately NOT one of the
    /// graph-wide `-Z` host-policy options — that protocol is closed (the
    /// sibling Targo's `VERIFIED_TARGO_HOST_POLICY_OPTIONS`, which it applies
    /// to the whole lane) — so crate mode transports it as
    /// the deliberately staged `TRUST_SPEC_EMIT_DIR` child env (after the
    /// ambient-authority scrub) and direct mode appends the typed
    /// `-Ztrust-dump=spec-clean:` sink to the compiler argv. Disclosure-only:
    /// the artifact can never change a verdict.
    spec_emit_dir: Option<&'a Path>,
}

fn verification_control_options(
    controls: &VerificationControls<'_>,
) -> Result<Vec<String>, String> {
    // The budget profile's bounds (determinism plan §3.2a/§3.6), passed
    // explicitly so the profile the report prints is the one the compiler ran:
    // the one COUNT that ends a search, then the two wall BACKSTOPS the
    // profile's backstop derives. The step budget is a seal constant targo
    // does not pass.
    let budget = controls.budget;
    let mut options = vec![
        format!("trust-verify-effort={}", budget.effort.conflicts_per_node),
        format!("trust-verify-timeout-ms={}", budget.backstop.vc_clock_ms()),
        format!("trust-verify-function-budget-ms={}", budget.backstop.function_clock_ms()),
        format!("trust-verify-session={}", controls.verification_session),
    ];
    // The worker-thread cap `--worker-threads` set, which the profile records
    // (not in its id): passed only when it caps, since 0 is the compiler's
    // own default (no cap).
    if budget.worker_threads != 0 {
        options.push(format!("trust-verify-worker-threads={}", budget.worker_threads));
    }
    let proof_artifact_root = controls.proof_artifact_root.to_str().ok_or_else(|| {
        format!(
            "proof artifact root is not valid UTF-8: {}",
            controls.proof_artifact_root.display()
        )
    })?;
    options.push(format!("trust-proof-artifact-root={proof_artifact_root}"));
    if let Some(policy) = controls.policy.option_value() {
        options.push(format!("trust-policy={policy}"));
    }
    // The profile is the sole carrier of hardened boundary obligations, so a
    // hardened run and a raw `trustc` run with the same profile now request
    // the same obligation set.
    if let Some(profile) = controls.hardened_profile {
        options.push(format!("trust-verify-profile={profile}"));
    }
    if options.iter().any(|option| option.contains('\x1f')) {
        return Err(
            "verifier control values cannot contain Cargo's U+001F encoded-rustflags delimiter"
                .to_string(),
        );
    }
    Ok(options)
}

fn append_verification_control_args(
    args: &mut Vec<String>,
    controls: &VerificationControls<'_>,
) -> Result<(), String> {
    for option in verification_control_options(controls)? {
        args.push("-Z".to_string());
        args.push(option);
    }
    Ok(())
}

/// Remove retired ambient compiler controls from the proof subprocess. Every
/// supported proof-affecting choice is carried by a tracked `-Z` option above;
/// allowing an inherited legacy variable as a second control plane would make
/// the report, Cargo fingerprint, and verifier semantics disagree.
fn scrub_legacy_verifier_env(cmd: &mut Command) {
    for name in [
        "TRUST_VERIFY",
        "AY_DIRECT_SOLVE_TIMEOUT_MS",
        "AY_PATH",
        "TY_PATH",
        "TRUST_AY_PATH",
        "TRUST_AGGREGATE_PERTURB",
        "TRUST_BACKING_INVARIANTS",
        "TRUST_BRIDGE_GATE",
        "TRUST_CACHE_DIR",
        "TRUST_CALLEE_PERTURB",
        "TRUST_COMPILER_CACHE",
        "TRUST_DUMP_ONLY",
        "TRUST_HARDENED",
        "TRUST_INTERIOR_PERTURB",
        "TRUST_IR_FLIP",
        "TRUST_NATIVE_UNIVERSAL",
        "TRUST_NO_COMPILER_CACHE",
        "TRUST_PROFILE",
        "TRUST_PROP_UNSAT_WORK_BUDGET",
        "TRUST_PROVE_BUDGET_SECS",
        "TRUST_SOLVER",
        "TRUST_SPINE_CONTRACT_FLIP",
        "TRUST_SPINE_NATIVE_GEN",
        "TRUST_SPINE_VERDICT_FLIP",
        "TRUST_STRUCTFIELD_PERTURB",
        "TRUST_TEMPORAL_SINGLE_WRITER",
        "TRUST_TARGO_PREPARED_TESTS_EXPORT",
        "TRUST_TARGO_PREPARED_TESTS_SESSION",
        "TRUST_TARGO_PREPARED_TEST_SESSION",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
        "TRUST_TARGO_TEST_MONITOR_SESSION",
        "TRUST_TYPE_LOWERING_PRODUCED_NODE_BUDGET",
        "TRUST_TY_PATH",
        "TRUST_VCGEN_BUNDLE_ADT_BUDGET",
        "TRUST_VCGEN_GENERATION_WORK_BUDGET",
        "TRUST_VCGEN_WORK_BUDGET",
        "TRUST_VERIFY_FN_BUDGET_MS",
        "TRUST_VERIFY_HARDENED",
        "TRUST_VERIFY_INCLUDE_DEPENDENCIES",
        "TRUST_VERIFY_INCLUDE_GENERATED",
        "TRUST_VERIFY_MEMORY_SAFE",
        "TRUST_VERIFY_OUTPUT",
        "TRUST_VERIFY_POLICY",
        "TRUST_VERIFY_PRIMARY_ONLY",
        "TRUST_VERIFY_SURVEY",
        "TRUST_VERIFY_TIMEOUT_MS",
        "TRUST_VERIFY_WORKER_THREADS",
        "TRUST_WP_PATH",
        "TRUST_WAVE24_PERTURB",
        "LIBPATH",
        "SHLIB_PATH",
        "LDR_PRELOAD",
    ] {
        cmd.env_remove(name);
    }
    // A verified test process must not inherit dynamic-loader injection from
    // the outer shell. Native Targo reconstructs the platform's ordinary
    // library search path for each test executable after the build; ambient
    // LD_*/DYLD_* values are not part of the authorized artifact identity.
    for (name, _) in env::vars_os() {
        if name.to_str().is_some_and(|name| name.starts_with("LD_") || name.starts_with("DYLD_")) {
            cmd.env_remove(name);
        }
    }
}

/// Establish the internal Targo→trustc monitor-mode channel. The value is the
/// same random session nonce carried by tracked `-Ztrust-verify-session`, so
/// an inherited ambient variable cannot independently select different MIR.
fn apply_targo_test_monitor_session(
    cmd: &mut Command,
    cargo_test_mode: bool,
    verification_session: &str,
) {
    // The outer process grants Targo authority to route a monitor marker; it
    // never exposes the compiler-consumed marker globally. Native Targo
    // authenticates the nonce and re-adds TRUST_TARGO_TEST_MONITOR_SESSION
    // only to selected-package runtime compilation units.
    cmd.env_remove("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION");
    if cargo_test_mode {
        cmd.env("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION", verification_session);
    }
}

#[allow(clippy::too_many_arguments)]
fn configured_verified_cargo_child(
    program: &str,
    effective_args: &[String],
    original_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    requirements: &ProjectRequirementFlags,
    cargo_selection: &ResolvedCargoSelection,
    cargo_test_mode: bool,
    execution_authority: Option<(&Path, &str)>,
) -> Result<Command, ChildSetupError> {
    configured_verified_cargo_child_with_memory(
        program,
        effective_args,
        original_args,
        rustc_path,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        requirements,
        cargo_selection,
        cargo_test_mode,
        execution_authority,
        apply_crate_memory_coordination,
    )
}

#[allow(clippy::too_many_arguments)]
fn configured_verified_cargo_child_with_memory<F>(
    program: &str,
    effective_args: &[String],
    original_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    requirements: &ProjectRequirementFlags,
    cargo_selection: &ResolvedCargoSelection,
    cargo_test_mode: bool,
    execution_authority: Option<(&Path, &str)>,
    configure_memory: F,
) -> Result<Command, ChildSetupError>
where
    F: FnOnce(&mut Command, &[String], Option<&Path>) -> Result<(), ChildSetupError>,
{
    let mut cmd = Command::new(program);
    cmd.args(effective_args);
    scrub_proof_compiler_authority_env(&mut cmd);
    scrub_legacy_verifier_env(&mut cmd);
    apply_targo_test_monitor_session(&mut cmd, cargo_test_mode, controls.verification_session);
    apply_native_runtime_env(&mut cmd, rustc_path);
    cmd.env("TRUST_TARGO_VERIFY", "1");
    // Trust (v6/D1): the spec-goal artifact transport for crate mode. The
    // ambient-authority scrub above already removed any inherited value; only
    // this run's deliberate request survives. Env rather than rustflags
    // because the graph-wide `-Z` channel is a closed host-policy protocol,
    // and the emission itself is gated compiler-side on an enabled
    // verification walk, so dependency units (compiled `-Ztrust-verify=off`)
    // write nothing.
    if let Some(dir) = controls.spec_emit_dir {
        cmd.env("TRUST_SPEC_EMIT_DIR", dir);
    }
    apply_cargo_child_rustc_env(&mut cmd, rustc_path);
    apply_lane_flags_env(LaneFlagsInput {
        cmd: &mut cmd,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        requirements,
        cargo_args: effective_args,
    })?;
    configure_memory(&mut cmd, original_args, Some(cargo_selection.target_directory.as_path()))?;
    cmd.env_remove("TRUST_TARGO_PREPARED_TEST_SESSION");
    cmd.env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST");
    cmd.env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256");
    if let Some((authority, authority_sha256)) = execution_authority {
        cmd.env("TRUST_TARGO_PREPARED_TEST_SESSION", controls.verification_session);
        cmd.env("TRUST_TARGO_TEST_EXECUTION_MANIFEST", authority);
        cmd.env("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256", authority_sha256);
    }
    Ok(cmd)
}
/// A cryptographically random 256-bit nonce injected into rustflags for one
/// Cargo proof run, with the run's private proof-artifact root.
///
/// Targo keys every verified unit on the nonce (its fingerprint and its
/// `unit_id`), so this forces every selected target through trustc without
/// deleting the user's build artifacts. The terminal target inventory and
/// `fresh=false` artifact events remain the evidence that the invalidation
/// actually took effect. A unit Targo compiles with `-Ztrust-verify=off` leaves
/// both values out of its identity, so a kept target directory reuses those
/// dependencies across runs, as long as nothing else exported here changes
/// from run to run (`two_sessions_differ_only_in_the_per_run_transport_pair`).
struct VerificationSession {
    _artifact_root: tempfile::TempDir,
    artifact_root: PathBuf,
    id: String,
    proof_store: Option<trust_certify::proof_artifacts::ProofArtifactStore>,
}

impl Drop for VerificationSession {
    fn drop(&mut self) {
        if let Some(store) = &self.proof_store {
            // Completed mathematical proofs can survive a failure elsewhere
            // in the program. Keep their storage bounded on either exit path.
            let _ = store.maintain();
        }
    }
}

impl VerificationSession {
    fn create() -> std::io::Result<Self> {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).map_err(|error| {
            std::io::Error::other(format!(
                "operating-system randomness failed while creating verification session: {error}"
            ))
        })?;
        let id = nonce.iter().map(|byte| format!("{byte:02x}")).collect();
        let artifact_root =
            tempfile::Builder::new().prefix("trust-proof-artifact-root-").tempdir()?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let mut permissions = std::fs::symlink_metadata(artifact_root.path())?.permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(artifact_root.path(), permissions)?;
        }
        let canonical_artifact_root = artifact_root.path().canonicalize()?;
        let metadata = std::fs::symlink_metadata(&canonical_artifact_root)?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(std::io::Error::other(
                "verification proof artifact root is not a non-symlink directory",
            ));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            if metadata.permissions().mode() & 0o777 != 0o700 {
                return Err(std::io::Error::other(
                    "verification proof artifact root is not private (mode 0700)",
                ));
            }
        }
        Ok(Self {
            _artifact_root: artifact_root,
            artifact_root: canonical_artifact_root,
            id,
            proof_store: None,
        })
    }

    fn artifact_root(&self) -> &Path {
        &self.artifact_root
    }

    fn with_proof_store(mut self) -> Self {
        self.proof_store = crate::config::cargo_home().and_then(|home| {
            let store = trust_certify::proof_artifacts::ProofArtifactStore::open(&home).ok()?;
            store.prepare_session(self.artifact_root()).ok()?;
            Some(store)
        });
        self
    }

    fn publish_proof_hints(&self) {
        if let Some(store) = &self.proof_store {
            // A failed optional hint write cannot change this run's verdict.
            let _ = store.publish_session(self.artifact_root());
        }
    }
}

const TEST_EXECUTION_AUTHORITY_SCHEMA: &str = "trust.targo-test-execution-authority.v2";

#[derive(serde::Serialize)]
struct TestExecutionAuthorityManifest<'a> {
    schema: &'static str,
    verification_session: &'a str,
    target_directory: String,
    executables: Vec<TestExecutionAuthorityEntry>,
    prepared: Option<trust_test_execution::PreparedTests>,
}

#[derive(serde::Serialize)]
struct TestExecutionAuthorityEntry {
    target: String,
    path: String,
    sha256: String,
    size: u64,
}

#[derive(Debug)]
struct TestExecutionAuthority {
    path: PathBuf,
    target_directory: String,
    executables: Vec<CertifiedTestExecutableReport>,
    inventory_sha256: String,
    /// The native prepared plan this authority binds: where each harness's
    /// per-case results go (`crate::test_results`).
    plan: Option<trust_test_execution::PreparedTests>,
}

fn exact_test_executable_identity(path: &Path) -> Result<(PathBuf, String, u64), String> {
    let before = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect test executable `{}`: {error}", path.display()))?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(format!(
            "test executable `{}` is not a regular non-symlink file",
            path.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if before.permissions().mode() & 0o111 == 0 {
            return Err(format!("test artifact `{}` is not executable", path.display()));
        }
    }
    let canonical = path.canonicalize().map_err(|error| {
        format!("cannot canonicalize test executable `{}`: {error}", path.display())
    })?;
    let mut file = File::open(&canonical).map_err(|error| {
        format!("cannot open test executable `{}`: {error}", canonical.display())
    })?;
    let opened = file.metadata().map_err(|error| {
        format!("cannot inspect open test executable `{}`: {error}", canonical.display())
    })?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer).map_err(|error| {
            format!("cannot hash test executable `{}`: {error}", canonical.display())
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let after = std::fs::symlink_metadata(&canonical).map_err(|error| {
        format!("cannot re-inspect test executable `{}`: {error}", canonical.display())
    })?;
    let stable = !after.file_type().is_symlink()
        && after.file_type().is_file()
        && before.len() == opened.len()
        && opened.len() == after.len()
        && before.modified().ok() == opened.modified().ok()
        && opened.modified().ok() == after.modified().ok();
    #[cfg(unix)]
    let stable = {
        use std::os::unix::fs::MetadataExt as _;

        stable
            && before.dev() == opened.dev()
            && opened.dev() == after.dev()
            && before.ino() == opened.ino()
            && opened.ino() == after.ino()
    };
    if !stable {
        return Err(format!(
            "test executable `{}` changed while its phase-A identity was captured",
            canonical.display()
        ));
    }
    Ok((canonical, format!("{:x}", hasher.finalize()), opened.len()))
}

fn load_prepared_tests(
    session: &VerificationSession,
    target_directory: &str,
    entries: &[TestExecutionAuthorityEntry],
    receipt: Option<&trust_test_execution::PreparedTestsReceipt>,
) -> Result<Option<trust_test_execution::PreparedTests>, String> {
    use trust_test_execution::{MAX_PLAN_BYTES, PreparedTests, RECEIPT_SCHEMA};
    let Some(receipt) = receipt else {
        return Ok(None);
    };
    let path = session.artifact_root().join("prepared-tests.json");
    if receipt.schema != RECEIPT_SCHEMA
        || receipt.session != session.id
        || Path::new(&receipt.path) != path
    {
        return Err(
            "prepared test receipt does not match the current native compile session".into()
        );
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = options
        .open(&path)
        .map_err(|error| format!("cannot open native prepared tests: {error}"))?;
    let metadata = file.metadata().map_err(|error| error.to_string())?;
    if !metadata.is_file() || metadata.len() > MAX_PLAN_BYTES {
        return Err("invalid native prepared-test file".into());
    }
    let mut bytes = Vec::new();
    std::io::Read::by_ref(&mut file)
        .take(MAX_PLAN_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() as u64 > MAX_PLAN_BYTES
        || format!("{:x}", Sha256::digest(&bytes)) != receipt.sha256
    {
        return Err("native prepared-test bytes differ from the current Targo receipt".into());
    }
    let plan: PreparedTests = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    if plan.target_directory != target_directory {
        return Err("native prepared-test target directory changed".into());
    }
    let expected = entries
        .iter()
        .map(|entry| (entry.path.clone(), (entry.sha256.clone(), entry.size)))
        .collect();
    plan.validate(&session.id, &expected)?;
    Ok(Some(plan))
}

fn write_test_execution_authority(
    qualification: &QualifiedTestExecution,
    verification_session: &VerificationSession,
    target_directory: &Path,
    toolchain_root: &Path,
    executables: &BTreeSet<CargoTestExecutable>,
    prepared_receipt: Option<&trust_test_execution::PreparedTestsReceipt>,
) -> Result<TestExecutionAuthority, String> {
    qualification.require_session(&verification_session.id)?;
    if executables.is_empty() {
        return Err(
            "Cargo test compile phase emitted no selected-package test executables".to_string()
        );
    }
    let target_directory = target_directory.canonicalize().map_err(|error| {
        format!(
            "cannot canonicalize Cargo target directory `{}`: {error}",
            target_directory.display()
        )
    })?;
    let toolchain_root = toolchain_root.canonicalize().map_err(|error| {
        format!(
            "cannot canonicalize authenticated Trust toolchain root `{}`: {error}",
            toolchain_root.display()
        )
    })?;
    if target_directory.starts_with(&toolchain_root)
        || toolchain_root.starts_with(&target_directory)
    {
        return Err(format!(
            "Cargo target directory `{}` overlaps authenticated Trust toolchain root `{}`; project artifacts must not be able to masquerade as or mutate sysroot TCB artifacts",
            target_directory.display(),
            toolchain_root.display(),
        ));
    }
    let mut entries = Vec::with_capacity(executables.len());
    let mut paths = BTreeSet::new();
    let mut target_paths = BTreeMap::new();
    for executable in executables {
        if !executable.path.is_absolute() {
            return Err(format!(
                "selected test target `{}` emitted a non-absolute executable path `{}`",
                executable.target.report_label(),
                executable.path.display()
            ));
        }
        let (path, sha256, size) = exact_test_executable_identity(&executable.path)?;
        if sha256 != executable.phase_a_sha256 {
            return Err(format!(
                "selected test executable `{}` changed after native Targo published its phase-A byte identity (published sha256={}, observed sha256={})",
                path.display(),
                executable.phase_a_sha256,
                sha256,
            ));
        }
        if !path.starts_with(&target_directory) {
            return Err(format!(
                "selected test executable `{}` escapes Cargo target directory `{}`",
                path.display(),
                target_directory.display()
            ));
        }
        if !paths.insert(path.clone()) {
            return Err(format!(
                "Cargo emitted duplicate selected test executable `{}`",
                path.display()
            ));
        }
        if let Some(previous) = target_paths.insert(executable.target.clone(), path.clone()) {
            if previous != path {
                return Err(format!(
                    "selected Cargo target `{}` emitted ambiguous executable paths `{}` and `{}`",
                    executable.target.report_label(),
                    previous.display(),
                    path.display()
                ));
            }
        }
        let path = path.to_str().ok_or_else(|| {
            format!("test executable path `{}` is not valid UTF-8", path.display())
        })?;
        entries.push(TestExecutionAuthorityEntry {
            target: executable.target.report_label(),
            path: path.to_string(),
            sha256,
            size,
        });
    }
    entries.sort_by(|left, right| left.path.cmp(&right.path));
    let target_directory = target_directory.to_str().ok_or_else(|| {
        format!("Cargo target directory `{}` is not valid UTF-8", target_directory.display())
    })?;
    let manifest = TestExecutionAuthorityManifest {
        schema: TEST_EXECUTION_AUTHORITY_SCHEMA,
        verification_session: &verification_session.id,
        target_directory: target_directory.to_string(),
        prepared: load_prepared_tests(
            verification_session,
            target_directory,
            &entries,
            prepared_receipt,
        )?,
        executables: entries,
    };
    let serialized = serde_json::to_vec(&manifest)
        .map_err(|error| format!("cannot serialize test execution authority: {error}"))?;
    if serialized.len() as u64 > trust_test_execution::MAX_PLAN_BYTES {
        return Err("test execution authority exceeds its native size bound".into());
    }
    let path = verification_session.artifact_root().join("test-execution-authority.json");
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;

        options.mode(0o600);
    }
    let mut file = options
        .open(&path)
        .map_err(|error| format!("cannot create private test execution authority: {error}"))?;
    let inventory_sha256 = format!("{:x}", Sha256::digest(&serialized));
    file.write_all(&serialized)
        .map_err(|error| format!("cannot write private test execution authority: {error}"))?;
    file.sync_all().map_err(|error| format!("cannot persist test execution authority: {error}"))?;
    let plan = manifest.prepared.clone();
    let executables = manifest
        .executables
        .into_iter()
        .map(|entry| CertifiedTestExecutableReport {
            target: entry.target,
            path: entry.path,
            sha256: entry.sha256,
            size: entry.size,
        })
        .collect();
    Ok(TestExecutionAuthority {
        path,
        target_directory: manifest.target_directory,
        executables,
        inventory_sha256,
        plan,
    })
}

/// Resolve the `RUSTC` value pinned onto child cargo invocations.
///
/// Ambient overrides and compatibility aliases are never proof authority.
/// `trustc` now reports a rustc-compatible version identity directly, so Cargo
/// and build scripts no longer need a `rustc`-spelled copy, hard link, or
/// symlink. Pinning the already selected path also avoids rereading and
/// byte-comparing a mutable alias before each Cargo invocation.
pub(super) fn cargo_child_rustc_path(rustc_path: &Path) -> PathBuf {
    rustc_path.to_path_buf()
}

/// Pin `RUSTC` for a child cargo so dependency and build-script compiles use
/// the discovered Trust toolchain instead of whatever PATH resolution finds
/// (rustup shims have attempted component management against linked Trust
/// toolchains, destroying the link). Wrappers are explicitly disabled so they
/// cannot strip flags or forge compiler output.
fn apply_cargo_child_rustc_env(cmd: &mut Command, rustc_path: &Path) {
    let rustc = cargo_child_rustc_path(rustc_path);
    // Cargo exposes the same build.rustc setting through both variables;
    // CARGO_BUILD_RUSTC is the config-key spelling and can otherwise win over
    // a pinned RUSTC. Pin both to one authenticated compiler.
    cmd.env("RUSTC", &rustc);
    cmd.env("CARGO_BUILD_RUSTC", rustc);
    cmd.env("RUSTC_WRAPPER", "");
    cmd.env("RUSTC_WORKSPACE_WRAPPER", "");
    cmd.env("CARGO_BUILD_RUSTC_WRAPPER", "");
    cmd.env("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "");
}

fn cargo_compiler_override_diagnostic(args: &[String]) -> Option<String> {
    for variable in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"] {
        if env::var_os(variable).as_deref().is_some_and(|value| value.to_str().is_none()) {
            return Some(format!(
                "{variable} is not valid Unicode; evidence-grade Targo cannot preserve its compiler-argument boundaries"
            ));
        }
    }
    for variable in [
        "RUSTC",
        "CARGO_BUILD_RUSTC",
        "RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        if env::var_os(variable).is_some_and(|value| !value.is_empty()) {
            return Some(format!(
                "{variable} is set; evidence-grade Targo invocations require the selected sibling trustc with no compiler wrapper (unset {variable})"
            ));
        }
    }
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--" {
            break;
        }
        let value = if arg == "--config" {
            index += 1;
            args.get(index).map(String::as_str)
        } else {
            arg.strip_prefix("--config=")
        };
        if let Some(value) = value {
            let key = value.split('=').next().unwrap_or_default().trim().to_ascii_lowercase();
            if key == "build.rustc"
                || key == "build.rustc-wrapper"
                || key == "build.rustc-workspace-wrapper"
                || (key.starts_with("target.")
                    && (key.ends_with(".rustc")
                        || key.ends_with(".rustc-wrapper")
                        || key.ends_with(".rustc-workspace-wrapper")))
            {
                return Some(format!(
                    "Cargo config override `{key}` is not permitted in an evidence-grade compiler invocation"
                ));
            }
        }
        index += 1;
    }
    // A config-file `build.rustc` / `rustc-wrapper` is invisible here, but it
    // is overridden rather than refused: the verified build
    // (`apply_cargo_child_rustc_env`) and every package-selection probe
    // (`cargo_selection::selection_probe_command`) pin RUSTC and
    // CARGO_BUILD_RUSTC to the authenticated compiler and empty the wrapper
    // variables, so it never runs.
    //
    // `[host]` rustflags are the one rustflags channel that neither the
    // exported RUSTFLAGS nor the selection probes' rustflags override; refuse
    // external code there (in any config file, `include` chain or variable,
    // and any Cargo config that cannot be examined) before any Cargo process,
    // the package-selection probe included, starts.
    super::kani_gate::inherited_host_rustflags_refusal(args)
}

/// A per-function verification row parsed from the compiler's TRUST_JSON
/// transport. Synthetic transport bookkeeping rows (`transport:*` kinds, e.g.
/// the `<transport>` missing-json placeholder) do not count as evidence that
/// verification ran.
fn is_per_function_verification_row(result: &VerificationResult) -> bool {
    !result.kind.starts_with("transport:")
}

/// Hard-error diagnostic for a run that collected no authenticated evidence
/// that verification actually executed. A real per-function row or coverage
/// summary proves that trustc ran; Cargo crate mode may additionally rely on
/// its authenticated terminal primary-target inventory for a valid empty
/// crate. Raw single-file mode has no Cargo inventory and therefore requires a
/// row or coverage summary even in an advisory lane. This prevents a replaced,
/// stale, or early-exiting compiler from turning an empty transport into a
/// successful zero-obligation report.
pub(super) fn missing_trust_json_diagnostic(
    crate_mode: bool,
    results: &[VerificationResult],
    completed_proof_targets: &BTreeSet<CargoTargetIdentity>,
    has_authenticated_coverage_summary: bool,
) -> Option<String> {
    if results.iter().any(is_per_function_verification_row)
        || has_authenticated_coverage_summary
        || (crate_mode && !completed_proof_targets.is_empty())
    {
        return None;
    }
    Some(
        "verification did not run: no per-function TRUST_JSON transport row, authenticated \
         coverage summary, or terminal Cargo target inventory was collected\n\
         Likely causes:\n\
         - the unique `-Z trust-verify-session` compiler-session rustflag did not reach the compiler or an authenticated primary target\n\
         - the linked Trust Cargo frontend (sibling `targo` next to trustc) is missing or was bypassed\n\
         - the selected source or Cargo targets did not invoke trustc\n\
         Note: targo-trust injects a unique compiler-session rustflag and rejects selected `fresh=true` artifacts; a warm Cargo cache is not accepted as proof evidence."
            .to_string(),
    )
}

// ---------------------------------------------------------------------------
// Build command
// ---------------------------------------------------------------------------

/// Build the command for a built local Trust compiler.
#[cfg(test)]
pub(crate) fn build_native_command(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> Vec<String> {
    build_native_command_with_json_transport(rustc, subcommand, sub_args, config, None, true)
        .expect("test command fixtures should include sibling targo for crate mode")
}

pub(crate) fn build_native_command_with_json_transport(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> Result<Vec<String>, String> {
    if sub_args.is_single_file {
        // Direct rustc invocation for a single .rs file. Verification is
        // batteries-on and the compiler's default `unscoped` role is in scope;
        // raw invocations never forge Cargo-owned role/package metadata.
        validate_direct_rustc_passthrough(&sub_args.passthrough)?;
        let strict_artifact_policy = sub_args.strict_artifact_policy();
        let passthrough = if strict_artifact_policy {
            canonicalize_strict_safety_codegen_args(&sub_args.passthrough).map_err(
                |override_arg| {
                    format!(
                        "passthrough argument `{override_arg}` conflicts with strict verification's required overflow checks and debug assertions"
                    )
                },
            )?
        } else {
            sub_args.passthrough.clone()
        };
        let direct_target = direct_rustc_target(&passthrough)?;
        if selected_codegen_backend == Some("trust-cg") {
            if let Some(target) = direct_target {
                // Trust-CG rejects every custom target (and every unaudited
                // built-in target) outright. Apply that stronger policy before
                // trying to inspect a target file so an absent custom target
                // cannot obscure the authoritative matrix diagnostic.
                validate_trust_cg_effective_target(target)?;
            }
        }
        if let Some(target) = direct_target {
            validate_direct_custom_target_extension_tcb(target)?;
        }
        let passthrough = if selected_codegen_backend == Some("trust-cg") {
            validate_direct_trust_cg_rlib_target(&passthrough).map_err(|detail| {
                format!("trust-cg can currently link only an explicit rlib target: {detail}")
            })?;
            canonicalize_trust_cg_codegen_args(&passthrough).map_err(|override_arg| {
                format!(
                    "passthrough argument `{override_arg}` conflicts with trust-cg's required -Cpanic=abort, -Cdebuginfo=0, -Ccodegen-units=1, non-incremental contract"
                )
            })?
        } else {
            passthrough
        };
        let mut cmd_args = vec![
            rustc.to_string_lossy().to_string(),
            "-Z".to_string(),
            format!("trust-verify-level={}", level_to_num(&config.level)),
        ];
        if supports_json_transport {
            cmd_args.push("-Z".to_string());
            cmd_args.push("trust-verify-output=json".to_string());
        }
        append_verification_mode_args(&mut cmd_args, sub_args.allow_l0_gaps_lane());
        append_codegen_backend_args(
            &mut cmd_args,
            selected_codegen_backend,
            sub_args.allow_l0_gaps_lane(),
        );
        cmd_args.extend(passthrough);
        if selected_codegen_backend == Some("trust-cg") {
            append_trust_cg_codegen_args(&mut cmd_args);
        }
        if strict_artifact_policy {
            // Append last so the effective direct-rustc policy is obvious in
            // captured argv. Explicit user attempts to own either option were
            // rejected above rather than silently reordered.
            append_strict_safety_check_args(&mut cmd_args);
        }
        if !matches!(subcommand, Subcommand::Build | Subcommand::Test)
            && !has_output_path_flag(&sub_args.passthrough)
        {
            cmd_args.push("-o".to_string());
            cmd_args
                .push(temp_single_file_output_path(&sub_args.passthrough).display().to_string());
        }
        Ok(cmd_args)
    } else {
        // targo-based invocation for a crate.
        let cargo_cmd = match subcommand {
            Subcommand::Check | Subcommand::Report | Subcommand::Loop => {
                // Check-shaped subcommands run Cargo `check`, not `build`.
                //
                // This arm used to say `build`, on the ground that TrustVerify
                // runs over optimized MIR and "`cargo check` can stop before
                // that pipeline". That described stock rustc, whose check mode
                // demands `optimized_mir` only for the bodies metadata encoding
                // needs. It stopped describing trustc when the scope-truncation
                // fix moved verification out of codegen: `rustc_interface::
                // passes::analysis` calls `rustc_mir_transform::
                // trust_ensure_whole_crate_verification`, which
                // `ensure_done().optimized_mir(..)` for EVERY eligible local
                // body, before any fatal gate and with no
                // `output_types.should_codegen()` condition (the only such
                // condition in that module guards the `TRUST_DUMP_MONO`
                // observational dump). `analysis` runs under
                // `--emit=dep-info,metadata` exactly as under `link`, and the
                // transport crate summary is emitted after the crate callback
                // completes whether or not codegen ran, so a check-mode unit
                // carries the complete inventory. Targo tags such units
                // `compile_mode = proof_unit_mode = "check"` (`"check-test"`
                // for test targets), which the transport accepts at every
                // validation site; nothing on this path opens an rlib, an
                // object file, or a linked executable — test executables are
                // read only under `cargo_test_mode`.
                //
                // What `build` bought, then, was codegen: argv showed
                // `--emit=dep-info,metadata,link`, and LLVM ran for every unit
                // the operator only asked to verify. Measured (unverified A/B
                // on the current seal, same crate): the `ay_dpll` test unit
                // took 7.47 GiB / 241 s under `build` against 4.58 GiB / 41 s
                // under `check`; the lib unit moved the same way. That codegen
                // memory is exactly what `-Ztrust-verify-memory-ceiling-bytes`
                // (physmem/8, injected by `verification_control_options`)
                // cannot bound — its help text says it observes only the
                // verifier's instrumented poll points, never LLVM — and the
                // ceiling was measured exceeded 3.8x under `build`. Dropping
                // codegen from `check` is therefore both the 6x time win on the
                // worst unit and what lets the per-process ceiling hold, which
                // is what gates raising the fan-out from 4 toward this host's
                // 18 cores (see `apply_memory_aware_job_bound` below).
                //
                // `report` and `loop` reach this arm only through a direct
                // caller: `main.rs` remaps both to `Check` before the pipeline
                // builds argv (`report` renders the check's transport; `loop`
                // re-runs the check each iteration), so they follow it here.
                // One lane deliberately not served: `--backend trust-cg`'s
                // output-preservation gate (`-Ztrust-cg-output-gate`) is a
                // codegen-time check and cannot fire under `check`; `build` is
                // the lane that exercises it.
                "check"
            }
            Subcommand::Diff | Subcommand::Solvers => "check",
            Subcommand::Build => "build",
            Subcommand::Test => "test",
        };
        let targo = native_trust_cargo_path(rustc)?;
        let mut cargo_args = sub_args.crate_mode_cargo_args();
        if let Some(error) = cargo_compiler_override_diagnostic(&cargo_args) {
            return Err(error);
        }
        if selected_codegen_backend == Some("trust-cg") {
            let effective_target = if let Some(target) =
                effective_cargo_target_with_targo(&cargo_args, &targo, rustc)?
            {
                target
            } else {
                let host = exact_rustc_host_triple(rustc)?;
                insert_cargo_option_before_separator(&mut cargo_args, "--target", host.clone());
                host
            };
            validate_trust_cg_effective_target(&effective_target)?;
            let cargo_rustc = cargo_child_rustc_path(rustc);
            preflight_trust_cg_cargo_targets_with_targo(
                &cargo_args,
                &targo,
                &cargo_rustc,
                sub_args.strict_artifact_policy(),
            )?;
        }
        let mut cmd_args = vec![targo.to_string_lossy().to_string(), cargo_cmd.to_string()];
        // Trust: bound the Cargo fan-out's width. Without this the verified
        // gate runs at Cargo's default `-j ncpu` — 18 here — and this tree has
        // two recorded fatalities from exactly that: `hw.ncpu` panicking a
        // 24 GB host (`trust_added::run_quick`) and 14 threads dying to
        // SIGKILL on a 48 GB host (`trust_extra`). `memory_aware_jobs` was
        // already the policy for both dev diagnostics; the user-facing
        // verified pipeline is where it actually has to hold.
        //
        // Read `trust_added::jobs_for_host` before assuming this fixes the
        // `ay_arrays` SIGKILL that prompted it. It does not: on the sampled
        // trace every instant above 60 GiB co-resident carried 3 to 5 live
        // units, so a cap of 9 binds at no pressure instant there. What it
        // bounds is the wide fan-out, which the 69-member workspace reaches
        // and the sampled `-p` graph mostly did not.
        //
        // Operator override wins: an explicit `-j`/`--jobs` in any Cargo
        // spelling, `CARGO_BUILD_JOBS`, or `[build] jobs` in a Cargo config
        // file suppresses the injection entirely rather than being appended
        // after and silently outranked. A gate that quietly ignores the
        // parallelism it was told to use would be lying about what it ran,
        // which is worse than running too wide.
        let operator_selected_jobs = cargo_jobs_explicitly_selected(&cargo_args);
        apply_memory_aware_job_bound(
            &mut cargo_args,
            operator_selected_jobs,
            crate::trust_added::memory_aware_jobs(),
        );
        cmd_args.extend(cargo_args);
        // RUSTC and the lane are set via env in run_compiler /
        // run_compiler_capture (apply_cargo_child_rustc_env +
        // apply_lane_flags_env).
        Ok(cmd_args)
    }
}

pub(super) fn exact_rustc_host_triple(rustc: &Path) -> Result<String, String> {
    exact_rustc_host_triple_budget(rustc, None)
}

pub(super) fn exact_rustc_host_triple_until(
    rustc: &Path,
    deadline: Instant,
) -> Result<String, String> {
    super::project_policy::remaining(deadline)?;
    let result = exact_rustc_host_triple_budget(rustc, Some(deadline));
    super::project_policy::remaining(deadline)?;
    result
}

fn exact_rustc_host_triple_budget(
    rustc: &Path,
    deadline: Option<Instant>,
) -> Result<String, String> {
    let mut command = Command::new(rustc);
    command.arg("-vV").env_clear();
    let cap = crate::bounded_process::resolve_probe_deadline(Duration::from_secs(10));
    let timeout = match deadline {
        Some(deadline) => super::project_policy::remaining(deadline)?.min(cap),
        None => cap,
    };
    let output = crate::bounded_process::output_with_exact_deadline(
        &mut command,
        &format!("selected compiler {} -vV host probe", rustc.display()),
        64 * 1024,
        timeout,
    )?;
    if !output.status.success() {
        return Err(format!("{} -vV failed with {}", rustc.display(), output.status));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| format!("{} -vV output was not valid UTF-8", rustc.display()))?;
    let hosts = stdout.lines().filter_map(|line| line.strip_prefix("host: ")).collect::<Vec<_>>();
    let [host] = hosts.as_slice() else {
        return Err(format!(
            "{} -vV must report exactly one host triple, observed {}",
            rustc.display(),
            hosts.len()
        ));
    };
    if host.is_empty()
        || host.len() > 255
        || host.trim() != *host
        || !host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(format!("{} -vV reported invalid host triple `{host}`", rustc.display()));
    }
    Ok((*host).to_string())
}

/// Splice the memory-aware job count into a crate-mode Cargo argv, unless the
/// operator has already chosen one.
///
/// Split out from the argv assembly so both branches are testable without an
/// ambient Cargo configuration: whether an operator selection exists is a
/// property of the process environment (cwd, `CARGO_BUILD_JOBS`, config files)
/// that a unit test cannot vary safely while other tests run in parallel.
fn apply_memory_aware_job_bound(
    cargo_args: &mut Vec<String>,
    operator_selected_jobs: bool,
    jobs: usize,
) {
    if operator_selected_jobs {
        return;
    }
    insert_cargo_option_before_separator(cargo_args, "-j", jobs.to_string());
}

/// Trust: has the operator already chosen Cargo's job count?
///
/// Covers all three places Cargo takes one from: the command line before the
/// `--` separator (`-j N`, `-jN`, `-j=N`, `--jobs N`, `--jobs=N`), the
/// `CARGO_BUILD_JOBS` environment variable, and `[build] jobs` in a Cargo
/// config file. All three are deliberately broad rather than exact: a false
/// positive only restores Cargo's own default, while a false negative would
/// append a second `-j` after the operator's and win Cargo's last-wins parse,
/// which is the failure this guard exists to prevent.
///
/// The config-file arm is not hypothetical. This repository's own
/// `.cargo/config.toml` carries `[build] jobs = 4`, with a comment naming this
/// host's shared 128 GiB UMA pool as the reason; injecting `-j 9` over it
/// would have silently run the gate at more than twice the width its operator
/// asked for.
pub(crate) fn cargo_jobs_explicitly_selected(args: &[String]) -> bool {
    cargo_jobs_explicitly_selected_with(
        args,
        env::var_os("CARGO_BUILD_JOBS").as_deref(),
        cargo_config_files_select_jobs(),
    )
}

/// The decision behind [`cargo_jobs_explicitly_selected`], with Cargo's job
/// environment and config-file answer passed in so it can be tested without
/// mutating process-global state that parallel tests share.
fn cargo_jobs_explicitly_selected_with(
    args: &[String],
    build_jobs_env: Option<&OsStr>,
    config_selects_jobs: bool,
) -> bool {
    if build_jobs_env.is_some_and(|value| !value.is_empty()) {
        return true;
    }
    if config_selects_jobs {
        return true;
    }
    args.iter()
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| arg.starts_with("-j") || arg == "--jobs" || arg.starts_with("--jobs="))
}

/// Does any Cargo config file on Cargo's own search path select `build.jobs`?
///
/// Cargo searches `.cargo/config.toml` (and the legacy `.cargo/config`) in the
/// invocation directory and every ancestor, then `$CARGO_HOME`. The Cargo
/// child here inherits this process's working directory — nothing in this file
/// sets `current_dir` on it — so this process's cwd is the same search root
/// Cargo will use.
fn cargo_config_files_select_jobs() -> bool {
    let Ok(cwd) = env::current_dir() else {
        // Without a cwd this cannot tell what Cargo would read. Assume the
        // operator has spoken; the cost is Cargo's default width, not a
        // silently overridden selection.
        return true;
    };
    let cargo_home = env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")));
    cargo_config_search_selects_jobs(&cwd, cargo_home.as_deref())
}

/// Search every ancestor, as Cargo does, without imposing a workspace boundary.
fn cargo_config_search_selects_jobs(start: &Path, cargo_home: Option<&Path>) -> bool {
    cargo_config_dirs_select_jobs(start.ancestors(), cargo_home)
}

/// Scan the supplied search directories. Tests provide only owned fixture
/// ancestors, so an operator's real config cannot change the fixture's answer.
fn cargo_config_dirs_select_jobs<'a>(
    ancestors: impl IntoIterator<Item = &'a Path>,
    cargo_home: Option<&Path>,
) -> bool {
    ancestors.into_iter().any(|dir| cargo_config_dir_selects_jobs(&dir.join(".cargo")))
        || cargo_home.is_some_and(cargo_config_dir_selects_jobs)
}

/// `config.toml` then the legacy extensionless `config`, as Cargo reads them.
fn cargo_config_dir_selects_jobs(cargo_dir: &Path) -> bool {
    ["config.toml", "config"]
        .iter()
        .any(|name| cargo_config_file_selects_jobs(&cargo_dir.join(name)))
}

/// Read one Cargo config file and decide whether it selects `build.jobs`.
///
/// A file that exists but cannot be read or is implausibly large counts as a
/// selection. That is the conservative direction: the alternative is to
/// override a selection this code simply failed to look at.
fn cargo_config_file_selects_jobs(path: &Path) -> bool {
    /// A Cargo config far past any plausible size is not read into memory.
    const MAX_CARGO_CONFIG_BYTES: u64 = 1 << 20;

    match path.metadata() {
        Err(_) => false,
        Ok(metadata) if !metadata.is_file() => false,
        Ok(metadata) if metadata.len() > MAX_CARGO_CONFIG_BYTES => true,
        Ok(_) => match std::fs::read_to_string(path) {
            Ok(text) => cargo_config_text_selects_jobs(&text),
            Err(_) => true,
        },
    }
}

/// Does this Cargo config text set `build.jobs`?
///
/// A deliberately small TOML-shaped scan, not a parser: `jobs` as a key under
/// a `[build]` table header, or the dotted `build.jobs` spelling at top level.
/// Over-matching costs only Cargo's default job count.
fn cargo_config_text_selects_jobs(text: &str) -> bool {
    let mut in_build_table = false;
    for raw_line in text.lines() {
        let line = raw_line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line.strip_prefix('[').and_then(|rest| rest.strip_suffix(']')) {
            in_build_table = header.trim() == "build";
            continue;
        }
        let Some((key, _)) = line.split_once('=') else {
            continue;
        };
        let key = key.trim().trim_matches('"');
        if (in_build_table && key == "jobs") || key == "build.jobs" {
            return true;
        }
    }
    false
}

fn insert_cargo_option_before_separator(args: &mut Vec<String>, option: &str, value: String) {
    let index = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    args.splice(index..index, [option.to_string(), value]);
}

// ---------------------------------------------------------------------------
// Compiler execution
// ---------------------------------------------------------------------------

/// Bounded, diagnostic-only failure context. This never carries report rows,
/// receipts, or a capability that can contribute to a measurement.
#[derive(Debug, Default)]
pub(crate) struct CompilerRunDiagnostics {
    pub(crate) errors: Vec<CompilerDiagnostic>,
    pub(crate) truncated: bool,
    /// Requested audit output failed; this is never a proof or compiler verdict.
    pub(crate) artifact_failed: bool,
}

impl CompilerRunDiagnostics {
    const MAX_ERRORS: usize = 8;
    const MAX_MESSAGE_BYTES: usize = 2048;

    pub(crate) fn extend(&mut self, diagnostics: &Self) {
        self.capture(&diagnostics.errors);
        self.truncated |= diagnostics.truncated;
        self.artifact_failed |= diagnostics.artifact_failed;
    }

    fn capture(&mut self, diagnostics: &[CompilerDiagnostic]) {
        for diagnostic in
            diagnostics.iter().filter(|d| matches!(d.level.as_str(), "error" | "fatal"))
        {
            let suffix = " [truncated]";
            let limit = if diagnostic.message.len() > Self::MAX_MESSAGE_BYTES {
                Self::MAX_MESSAGE_BYTES - suffix.len()
            } else {
                Self::MAX_MESSAGE_BYTES
            };
            let mut end = diagnostic.message.len().min(limit);
            while !diagnostic.message.is_char_boundary(end) {
                end -= 1;
            }
            let mut message = diagnostic.message[..end].to_string();
            if end < diagnostic.message.len() {
                message.push_str(suffix);
                self.truncated = true;
            }
            if self.errors.iter().any(|d| d.level == diagnostic.level && d.message == message) {
                continue;
            }
            if self.errors.len() == Self::MAX_ERRORS {
                self.truncated = true;
                continue;
            }
            self.errors.push(CompilerDiagnostic { level: diagnostic.level.clone(), message });
        }
    }
}

pub(crate) type CompilerDiagnosticObserver<'a> = &'a mut dyn FnMut(&CompilerRunDiagnostics);

fn observe_compiler_errors(
    observer: &mut Option<CompilerDiagnosticObserver<'_>>,
    errors: &[CompilerDiagnostic],
) {
    if let Some(observer) = observer.as_mut() {
        let mut diagnostics = CompilerRunDiagnostics::default();
        diagnostics.capture(errors);
        if !diagnostics.errors.is_empty() {
            observer(&diagnostics);
        }
    }
}

/// Keep the existing stderr error while allowing in-process diagnostic users
/// to explain an early setup refusal without inventing a report.
pub(crate) fn observe_setup_failure(
    observer: &mut Option<CompilerDiagnosticObserver<'_>>,
    message: String,
) {
    observe_compiler_errors(observer, &[CompilerDiagnostic { level: "error".into(), message }]);
}

pub(crate) fn report_setup_failure(
    observer: &mut Option<CompilerDiagnosticObserver<'_>>,
    message: std::fmt::Arguments<'_>,
) {
    let message = message.to_string();
    eprintln!("{message}");
    observe_setup_failure(observer, message);
}

fn report_artifact_failure(
    observer: &mut Option<CompilerDiagnosticObserver<'_>>,
    message: std::fmt::Arguments<'_>,
) {
    let message = message.to_string();
    eprintln!("{message}");
    if let Some(observer) = observer.as_mut() {
        let mut diagnostics =
            CompilerRunDiagnostics { artifact_failed: true, ..Default::default() };
        diagnostics.capture(&[CompilerDiagnostic { level: "error".into(), message }]);
        observer(&diagnostics);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReportRendering {
    Suppressed,
    Stdout,
    ArtifactsOnly,
}

impl From<bool> for ReportRendering {
    fn from(render: bool) -> Self {
        if render { Self::Stdout } else { Self::Suppressed }
    }
}

pub(crate) type LiveReportConsumer<'a> =
    &'a mut dyn FnMut(&LiveCanonicalReport) -> Result<(), String>;

pub(crate) struct CompilerRun<'a> {
    pub(crate) cmd_args: &'a [String],
    pub(crate) rustc_path: &'a Path,
    pub(crate) config: &'a TrustConfig,
    pub(crate) selected_codegen_backend: Option<&'a str>,
    pub(crate) supports_json_transport: bool,
    pub(crate) strict_artifact_policy: bool,
    pub(crate) strict_result_gate: bool,
    /// `--certify`: the release gate. Selects `GateLane::Certify` (every
    /// non-proved bucket fatal) and `-Ztrust-policy=certify` (full static
    /// discharge in the compiler).
    pub(crate) certify_gate: bool,
    pub(crate) allow_l0_gaps: bool,
    pub(crate) memory_safe_policy: bool,
    pub(crate) survey: bool,
    pub(crate) hardened: bool,
    pub(crate) trust_profile: Option<&'a str>,
    /// Trust (v6/D1): request the compiler's kernel-graded Clean goal artifact
    /// in this directory (`targo trust spec --emit clean` reads it back).
    pub(crate) spec_emit_dir: Option<&'a Path>,
    pub(crate) dump_verifier_inputs: Option<&'a Path>,
    pub(crate) format: OutputFormat,
    pub(crate) report_dir: Option<&'a str>,
    pub(crate) unsafe_memory_report: Option<&'a UnsafeMemoryReportRequest>,
    /// Optional proof-consuming same-process workflow. The callback receives an
    /// opaque capability only after both final publication receipts validate.
    pub(crate) live_report_consumer: Option<LiveReportConsumer<'a>>,
    pub(crate) diagnostic_observer: Option<CompilerDiagnosticObserver<'a>>,
    /// Internal reducers can request sealed audit artifacts without writing
    /// per-crate reports to their consolidated stdout.
    pub(crate) render_output: ReportRendering,
    /// The command builder injected a disposable `-o` for a non-build
    /// single-file invocation. The runner owns and removes its directory.
    pub(crate) ephemeral_single_file_output: bool,
    /// `--test-target-panics`. `TestTargetPanicPolicy::Strict` (what an absent
    /// flag resolves to) leaves this whole run byte-identical to a build
    /// without the policy; see `crate::test_target_panics`.
    pub(crate) test_target_panics: TestTargetPanicPolicy,
    /// Live-edit-loop step 2 (DELTA): a crate-mode `check` snapshots each
    /// package's obligation record and prints what changed since the base
    /// (`crate::agent_delta`). `None` leaves the run's output as it was.
    pub(crate) agent_delta: Option<&'a crate::agent_delta::DeltaRequest>,
}

/// Trust: extract a `--manifest-path <path>` (or `=`-joined) value from cargo args.
fn cargo_manifest_path_arg(args: &[String]) -> Option<PathBuf> {
    CargoSelectionArgs::parse(args)
        .ok()
        .and_then(|selection| selection.manifest_path().map(Path::to_path_buf))
}

/// Return Cargo's explicit target-directory override, without interpreting
/// arguments after `--` (those belong to the compiled target). Cargo accepts
/// both spellings and gives this CLI value precedence over environment/config
/// values.
fn cargo_target_dir_arg(args: &[String]) -> Option<PathBuf> {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--" {
            break;
        } else if arg == "--target-dir" {
            if let Some(path) = iter.next().filter(|path| !path.is_empty()) {
                return Some(PathBuf::from(path));
            }
        } else if let Some(path) = arg.strip_prefix("--target-dir=").filter(|path| !path.is_empty())
        {
            return Some(PathBuf::from(path));
        }
    }
    None
}

/// Trust: env var naming the optional cross-process memory-jobserver token file.
/// Normal verified crate mode never exports it: Unix requires the authenticated
/// host daemon, while platforms that cannot establish the file authority's Unix
/// ownership/locking invariants fail before Cargo fan-out.
const TRUST_MEMORY_JOBSERVER_ENV: &str = "TRUST_MEMORY_JOBSERVER";

/// Trust: env var naming the `trustd` memory-coordination daemon's Unix socket.
/// Unix crate mode exports this only after the exact packaged daemon passes its
/// identity and readiness checks. It deliberately does not export the token-file
/// transport at the same time. A selected daemon failure stops solver dispatch
/// inside a worker; launcher failure prevents the Cargo fan-out from starting.
const TRUST_MEMORY_JOBSERVER_SOCK_ENV: &str = "TRUST_MEMORY_JOBSERVER_SOCK";

/// Historical daemon opt-out. Unix verified crate mode rejects a truthy opt-out
/// and strips every spelling before workers: without a lifetime exclusion lease,
/// a file-only run could race another run's live daemon and create two
/// aggregate-budget authorities.
#[cfg(unix)]
const TRUSTD_DISABLE_ENV: &str = "TRUSTD_DISABLE";

/// Trust: is the `trustd` daemon auto-start opted out via [`TRUSTD_DISABLE_ENV`]?
/// Truthy = set to anything other than empty / `0` / `false` / `no` / `off`.
#[cfg(unix)]
fn trustd_disabled() -> bool {
    match env::var(TRUSTD_DISABLE_ENV) {
        Ok(v) => {
            let v = v.trim();
            !(v.is_empty()
                || v.eq_ignore_ascii_case("0")
                || v.eq_ignore_ascii_case("false")
                || v.eq_ignore_ascii_case("no")
                || v.eq_ignore_ascii_case("off"))
        }
        Err(_) => false,
    }
}

/// Resolve the Cargo target directory for artifacts, snapshots, and execution
/// manifests. Memory admission deliberately no longer derives authority from
/// this path. Honors Cargo's explicit `--target-dir` override first, then the
/// authoritative `target_directory` returned by the already-required
/// authenticated sibling `targo metadata` invocation. That value incorporates
/// Cargo's effective environment/config precedence. Direct environment and
/// manifest/cwd fallbacks exist only for unit-level callers without metadata.
pub(crate) fn cargo_target_dir(args: &[String], resolved_target_dir: Option<&Path>) -> PathBuf {
    if let Some(dir) = cargo_target_dir_arg(args) {
        return dir;
    }
    if let Some(dir) = resolved_target_dir.filter(|dir| !dir.as_os_str().is_empty()) {
        return dir.to_path_buf();
    }
    if let Some(dir) = env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        return PathBuf::from(dir);
    }
    if let Some(dir) = env::var_os("CARGO_BUILD_TARGET_DIR").filter(|v| !v.is_empty()) {
        return PathBuf::from(dir);
    }
    let manifest_dir = cargo_manifest_path_arg(args)
        .and_then(|m| m.parent().map(Path::to_path_buf))
        .or_else(nearest_manifest_dir_from_cwd)
        .unwrap_or_else(|| PathBuf::from("."));
    manifest_dir.join("target")
}

/// Resolve the observational last-results snapshot root. Cargo metadata is the
/// authority for the effective target directory, except for its default
/// workspace collapse: when exactly one non-root member is selected it reports
/// `<workspace>/target`, while this per-unit snapshot belongs under the
/// selected member's source root. Explicit/custom target directories retain
/// Cargo's resolution.
fn verification_cache_target_dir(
    args: &[String],
    cargo_selection: Option<&ResolvedCargoSelection>,
) -> Option<PathBuf> {
    verification_cache_target_dir_with_env(args, cargo_selection, |key| env::var_os(key))
}

fn verification_cache_target_dir_with_env(
    args: &[String],
    cargo_selection: Option<&ResolvedCargoSelection>,
    env_var: impl Fn(&str) -> Option<std::ffi::OsString>,
) -> Option<PathBuf> {
    if let Some(selection) = cargo_selection {
        if cargo_target_dir_arg(args).is_some() {
            return Some(cargo_target_dir(args, Some(&selection.target_directory)));
        }
        if let [package] = selection.packages.as_slice() {
            let metadata_parent = selection.target_directory.parent();
            let is_default_workspace_target = selection.target_directory.file_name()
                == Some(OsStr::new("target"))
                && metadata_parent.is_some_and(|parent| {
                    parent != package.root && package.root.starts_with(parent)
                });
            if is_default_workspace_target {
                return Some(package.root.join("target"));
            }
        }
        return Some(selection.target_directory.clone());
    }

    // Single-file mode has no Cargo metadata. Cargo's target-directory
    // environment still names where build output belongs; only without it
    // does the snapshot fall back beside the source.
    let source_target = args
        .iter()
        .find(|arg| arg.ends_with(".rs") && !arg.starts_with('-'))
        .and_then(|source| std::fs::canonicalize(source).ok())
        .and_then(|source| source.parent().map(|parent| parent.join("target")))?;
    Some(single_file_target_dir_from(env_var).unwrap_or(source_target))
}

fn single_file_target_dir_from(
    env_var: impl Fn(&str) -> Option<std::ffi::OsString>,
) -> Option<PathBuf> {
    ["CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR"]
        .into_iter()
        .find_map(|key| env_var(key).filter(|value| !value.is_empty()))
        .map(PathBuf::from)
}

fn persist_verification_snapshot(
    args: &[String],
    cargo_selection: Option<&ResolvedCargoSelection>,
    results: &[VerificationResult],
) {
    let Some(target_dir) = verification_cache_target_dir(args, cargo_selection) else {
        return;
    };
    let Ok(json) = serde_json::to_vec(results) else { return };
    let path = target_dir.join("trust-cache/verification.json");
    // Observational only: publication is atomic and symlink-safe, but failure
    // to write this convenience snapshot never changes the proof verdict.
    let _ = crate::durable_io::atomic_write_private(&path, &json);
}

/// Walk up from the cwd to the nearest directory containing `Cargo.toml` —
/// cargo's own manifest resolution. Without this, a subdirectory invocation
/// computed a cwd-relative `./target`, leaking an empty target dir (and the
/// jobserver artifacts) into the caller's subdir instead of the crate root.
/// Caught by the native trust-added trustc-native root-resolution gate.
fn nearest_manifest_dir_from_cwd() -> Option<PathBuf> {
    let mut dir = env::current_dir().ok()?;
    loop {
        if dir.join("Cargo.toml").is_file() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// Trust: `trustd` daemon Unix-socket path for the crate-mode fan-out. The
/// endpoint is fixed inside one euid-owned 0700 runtime directory, independent
/// of Cargo target directories. Thus concurrent verified builds share one host
/// allowance instead of each admitting 70% of RAM. The coordinator helper alone
/// creates and validates that directory; callers must not `create_dir_all` it.
///
/// `TRUSTD_RUNTIME_DIR` ([`trust_router::coordinator::RUNTIME_DIR_ENV`])
/// relocates the endpoint into a caller-chosen private directory: a separate
/// memory domain, disclosed on every use. The fake-toolchain integration tests
/// need it: sharing the host endpoint made them race each other under
/// parallelism and refuse to run at all beside any real verified build.
#[cfg(unix)]
fn memory_jobserver_socket_path() -> Result<PathBuf, String> {
    let runtime_dir_env = trust_router::coordinator::RUNTIME_DIR_ENV;
    match env::var_os(runtime_dir_env) {
        Some(dir) if dir.is_empty() => Err(format!(
            "{runtime_dir_env} is set but empty; unset it to use the host memory domain"
        )),
        Some(dir) => {
            let socket = trust_router::coordinator::host_socket_path_in(Path::new(&dir))
                .map_err(|error| {
                    format!(
                        "{runtime_dir_env} does not name a usable private trustd runtime directory: {error}"
                    )
                })?;
            eprintln!(
                "targo trust: note: {runtime_dir_env} selects a separate trustd memory domain at {}; this run does not share the host memory budget with verified builds outside it",
                socket.display()
            );
            Ok(socket)
        }
        None => trust_router::coordinator::host_socket_path().map_err(|error| {
            format!("could not establish the private per-user trustd runtime directory: {error}")
        }),
    }
}

/// Derive crash-recovery tooling from the already selected Targo program. The
/// caller validates that Targo against the selected Trust compiler before this
/// coordinator path runs. Keep the derivation lexical so a `targo` compatibility
/// symlink still names the `trustd` in its selected sysroot, and require an
/// absolute path so the diagnostic can never recommend ambient PATH lookup.
#[cfg(unix)]
fn recovery_trustd_for_selected_targo(program: &OsStr) -> Result<PathBuf, String> {
    let targo = Path::new(program);
    if !targo.is_absolute() {
        return Err(format!(
            "selected Targo path `{}` is not absolute; refusing to suggest an ambient-PATH crash-recovery command",
            targo.display()
        ));
    }
    let bin = targo.parent().ok_or_else(|| {
        format!("selected Targo path `{}` has no same-sysroot bin directory", targo.display())
    })?;
    Ok(bin.join(format!("trustd{}", std::env::consts::EXE_SUFFIX)))
}

/// Why a verified compiler child could not be configured, which decides the
/// exit: a usage or setup error is 2; a trustd memory authority that could not
/// be established for this run means the run could not run (3,
/// [`crate::determinism_report::EXIT_COULD_NOT_RUN`]), and re-running once the
/// daemon retires or answers can succeed. An installation with no usable
/// sibling daemon is a setup error ([`DaemonStartFailure`]).
#[derive(Debug)]
pub(super) enum ChildSetupError {
    /// A usage or setup error: exit 2.
    Setup(String),
    /// The daemon that admits this run's solvers could not be established
    /// (another build's trustd owns the socket, the daemon did not answer, it
    /// exited early, or its spawn failed for a reason other than a missing or
    /// forbidden executable): exit 3.
    CouldNotRun(String),
}

impl ChildSetupError {
    /// The exit this refusal maps to: 2, or 3 for a run that could not run.
    fn exit_code(&self) -> u8 {
        match self {
            ChildSetupError::Setup(_) => 2,
            ChildSetupError::CouldNotRun(_) => crate::determinism_report::EXIT_COULD_NOT_RUN,
        }
    }

    /// Print the refusal under `context` (setup errors only; a could-not-run
    /// refusal says COULD NOT RUN) and return the exit it maps to.
    fn report(&self, context: &str) -> ExitCode {
        match self {
            ChildSetupError::Setup(error) => {
                eprintln!("targo trust: {context}: {error}");
            }
            ChildSetupError::CouldNotRun(error) => {
                eprintln!(
                    "targo trust: COULD NOT RUN: {error}. The run started no compiler, so it has \
                     no verdict"
                );
            }
        }
        ExitCode::from(self.exit_code())
    }
}

impl From<String> for ChildSetupError {
    fn from(error: String) -> Self {
        ChildSetupError::Setup(error)
    }
}

impl std::fmt::Display for ChildSetupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChildSetupError::Setup(error) | ChildSetupError::CouldNotRun(error) => {
                f.write_str(error)
            }
        }
    }
}

/// The trustd this targo-trust process selected, held for the rest of its
/// life. Every compiler unit of the run is told to use that daemon's socket,
/// and one can compile for longer than the daemon's idle bound before its first
/// admission; without the hold the daemon idles out under it, and the unit's
/// selected, fail-closed lane refuses every obligation it owns (the 0.11.0
/// consumer check of 2026-10-19: aterm's binary, 129 obligations, ECONNREFUSED
/// on the selected endpoint after a compile longer than that bound). Never
/// dropped: the kernel closes the lease's descriptor when this process exits
/// by any path, and the daemon's idle interval starts then. The process
/// includes a `targo trust test` run's test execution and the report, so a
/// newly promoted build meets "another trustd owns" until those end too.
#[cfg(unix)]
static SESSION_TRUSTD_LEASE: SessionLease<trust_router::coordinator::DaemonLease> =
    SessionLease::new();

/// Where [`apply_crate_memory_coordination_with`] keeps the lease it took on
/// the daemon whose socket it exported. Generic over the lease, so that seam's
/// tests can hold one whose drop they observe.
struct SessionLease<L>(Mutex<Option<L>>);

impl<L> SessionLease<L> {
    const fn new() -> Self {
        Self(Mutex::new(None))
    }

    /// Hold `lease`, and only then drop the one it replaces, outside the lock.
    /// A later compiler execution in the same run (a rewrite-loop iteration)
    /// took its lease while the earlier one was still held, so there is no
    /// instant the run holds none.
    #[cfg(unix)]
    fn hold(&self, lease: L) {
        let replaced = self.0.lock().unwrap_or_else(|error| error.into_inner()).replace(lease);
        drop(replaced);
    }
}

/// Configure the shared crate-mode memory coordinator for every compiler
/// execution path, including rewrite-loop capture iterations. Unix clears both
/// inherited transports and exports only an exact authenticated daemon socket,
/// whose daemon this process then holds for its whole life
/// ([`SESSION_TRUSTD_LEASE`]). Non-Unix currently has no authority satisfying
/// the required filesystem invariants, so it fails after non-compiling metadata
/// selection but before compilation, Cargo fan-out, or solver dispatch.
fn apply_crate_memory_coordination(
    cmd: &mut Command,
    args: &[String],
    resolved_target_dir: Option<&Path>,
) -> Result<(), ChildSetupError> {
    let inherited_token = env::var_os(TRUST_MEMORY_JOBSERVER_ENV);
    #[cfg(unix)]
    {
        #[cfg(test)]
        if TEST_MEMORY_COORDINATOR_READY.with(std::cell::Cell::get) {
            return apply_crate_memory_coordination_with(
                cmd,
                args,
                resolved_target_dir,
                inherited_token.as_deref(),
                true,
                |_| Ok::<(), std::convert::Infallible>(()),
                &SessionLease::new(),
            );
        }
        if trustd_disabled() {
            cmd.env_remove(TRUST_MEMORY_JOBSERVER_SOCK_ENV);
            cmd.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
            return Err(format!(
                "{TRUSTD_DISABLE_ENV} is unsafe for verified crate mode on Unix; unset it so the authenticated trustd authority can be established"
            )
            .into());
        }
        let retained =
            crate::tool_identity::retained_daemon_build().map_err(ChildSetupError::Setup)?;
        apply_crate_memory_coordination_with(
            cmd,
            args,
            resolved_target_dir,
            inherited_token.as_deref(),
            true,
            |socket| match retained {
                Some(build) => trust_router::coordinator::ensure_daemon_for_build(
                    socket,
                    build.release,
                    build.commit,
                ),
                None => trust_router::coordinator::ensure_daemon(socket),
            },
            &SESSION_TRUSTD_LEASE,
        )
    }
    #[cfg(not(unix))]
    {
        apply_crate_memory_coordination_with(
            cmd,
            args,
            resolved_target_dir,
            inherited_token.as_deref(),
            false,
            |_| Err::<(), _>("trustd is unavailable on non-Unix"),
            &SessionLease::new(),
        )
    }
}

#[cfg(all(test, unix))]
thread_local! {
    static TEST_MEMORY_COORDINATOR_READY: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Run a unit-test closure with daemon provisioning injected as successful.
///
/// This is a thread-local test seam, so transport/report regressions can reach
/// their intended post-launch gate without creating a process-global fake
/// daemon at the real per-user socket. Production builds contain no bypass.
#[cfg(all(test, unix))]
pub(super) fn with_test_memory_coordinator_ready<T>(body: impl FnOnce() -> T) -> T {
    struct Reset(bool);

    impl Drop for Reset {
        fn drop(&mut self) {
            TEST_MEMORY_COORDINATOR_READY.with(|ready| ready.set(self.0));
        }
    }

    TEST_MEMORY_COORDINATOR_READY.with(|ready| {
        let previous = ready.replace(true);
        let _reset = Reset(previous);
        body()
    })
}

/// Why starting the trustd memory authority failed, for the exit it maps to:
/// an installation the run cannot use is a setup error (2) — the sibling
/// daemon is missing, not executable, not authorizable or cannot be
/// identified, which re-running cannot change — and anything else is a daemon
/// that could not be established this time (3): another build's daemon owns
/// the socket, it did not answer, it exited early, or its spawn failed for a
/// reason other than a missing or forbidden executable.
trait DaemonStartFailure: std::fmt::Display {
    fn is_installation_defect(&self) -> bool {
        false
    }
}

#[cfg(unix)]
impl DaemonStartFailure for trust_router::coordinator::EnsureDaemonError {
    fn is_installation_defect(&self) -> bool {
        use trust_router::coordinator::EnsureDaemonError;
        match self {
            EnsureDaemonError::Disabled
            | EnsureDaemonError::CurrentExecutable { .. }
            | EnsureDaemonError::SiblingUnavailable { .. }
            | EnsureDaemonError::ExecutableAuthority { .. }
            | EnsureDaemonError::Identity { .. } => true,
            EnsureDaemonError::Spawn { source, .. } => matches!(
                source.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::PermissionDenied
            ),
            // An early exit, no readiness, an uninspectable child, and any
            // variant added later: the daemon could not run the work.
            _ => false,
        }
    }
}

impl DaemonStartFailure for String {}
impl DaemonStartFailure for &str {}
impl DaemonStartFailure for std::convert::Infallible {}

/// Holds the lease `ensure_daemon` took on the daemon whose socket it exported
/// in `session`, for as long as any unit may still ask that daemon for
/// admission.
fn apply_crate_memory_coordination_with<F, E, L>(
    cmd: &mut Command,
    _args: &[String],
    _resolved_target_dir: Option<&Path>,
    inherited_token: Option<&OsStr>,
    start_daemon: bool,
    ensure_daemon: F,
    session: &SessionLease<L>,
) -> Result<(), ChildSetupError>
where
    F: FnOnce(&Path) -> Result<L, E>,
    E: DaemonStartFailure,
{
    cmd.env_remove(TRUST_MEMORY_JOBSERVER_SOCK_ENV);
    cmd.env_remove(TRUST_MEMORY_JOBSERVER_ENV);

    #[cfg(unix)]
    {
        let _ = inherited_token;
        // Targo has already interpreted the opt-out before selecting this exact
        // daemon domain. Do not propagate even a false-looking spelling into
        // workers, whose lower-level compatibility shim recognizes only `1`.
        cmd.env_remove(TRUSTD_DISABLE_ENV);
        if !start_daemon {
            return Err(format!(
                "{TRUSTD_DISABLE_ENV} cannot select a file-only authority on Unix verified crate mode"
            )
            .into());
        }
        let socket_path = memory_jobserver_socket_path()?;
        // From here a refusal is the daemon's: the run could not run (exit 3),
        // and re-running once the daemon retires or answers can succeed;
        // except an installation that has no usable sibling daemon, which is a
        // setup error (2) re-running cannot change (`DaemonStartFailure`).
        let lease = match ensure_daemon(&socket_path) {
            Ok(lease) => lease,
            Err(provision_error) => {
                let recovery_trustd = recovery_trustd_for_selected_targo(cmd.get_program())?;
                // A LIVE incumbent and a STALE socket need opposite remedies, and
                // telling an operator to "stop any incompatible live daemon" in the
                // live case manufactures the very wreckage the recovery sentence
                // then describes: a signalled trustd abandons the solvers it
                // admitted and records DIRTY. After a toolchain promotion the live
                // case is the COMMON one — the previous seal's daemon still owns
                // the socket — so it gets its own advice: wait.
                let rendered_provision_error = provision_error.to_string();
                if rendered_provision_error.contains("another trustd owns") {
                    return Err(ChildSetupError::CouldNotRun(format!(
                        "could not establish the selected same-sysroot trustd memory authority at {}: {rendered_provision_error}; refusing to launch a split-authority Cargo fan-out. Another live trustd owns that socket and this run could not adopt it. After a toolchain promotion this is normally the previous seal's daemon, still running; it can also be this build's own daemon, for example one closing (past its idle proof it takes no new session) or one too slow to answer the handshake, and a re-run in a moment adopts or replaces that one. WAIT for it to retire — it self-exits once no build holds it and {} seconds pass without admission traffic, and STATUS/IDENTITY/PING are observational (they neither hold it nor refresh that clock), so polling while you wait is safe. Do NOT signal it: killing a trustd abandons every solver it admitted and records DIRTY, after which automatic restart is refused until an operator attests quiescence. That attestation — `{} --recover-after-crash --confirm-no-solvers --socket {}` — is correct ONLY for a daemon that already exited uncleanly, never as a way to take the socket from a running one",
                        socket_path.display(),
                        trust_router::coordinator::IDLE_TIMEOUT.as_secs(),
                        recovery_trustd.display(),
                        socket_path.display(),
                    )));
                }
                let refusal = format!(
                    "could not establish the selected same-sysroot trustd memory authority at {}: {provision_error}; refusing to launch a split-authority Cargo fan-out. Confirm the sibling trustd at `{}` is installed/executable. If the prior trustd exited uncleanly, first establish that every solver it admitted is gone, then invoke the absolute executable `{}` with arguments `--recover-after-crash --confirm-no-solvers --socket {}` and retry. This absolute sibling path avoids ambient PATH selection; path derivation alone does not prove distribution provenance, packaged byte identity, or execution identity",
                    socket_path.display(),
                    recovery_trustd.display(),
                    recovery_trustd.display(),
                    socket_path.display(),
                );
                return Err(if provision_error.is_installation_defect() {
                    ChildSetupError::Setup(refusal)
                } else {
                    ChildSetupError::CouldNotRun(refusal)
                });
            }
        };
        session.hold(lease);
        cmd.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, socket_path);
        Ok(())
    }

    #[cfg(not(unix))]
    {
        let _ = (inherited_token, start_daemon, ensure_daemon, session);
        Err(format!(
            "verified crate mode is unsupported on {}: no memory-admission authority satisfies the required Unix ownership and locking invariants; refusing to launch uncoordinated workers",
            std::env::consts::OS
        )
        .into())
    }
}

/// Convert Cargo's canonical selected packages into the names used by report
/// subject and dependency-TCB accounting. Targo derives proof scope from this
/// resolved unit graph and carries role/package strings only as reporting
/// metadata; excluded units receive the explicit compiler off-switch.
/// Canonical selection handles package globs, workspace defaults/excludes,
/// partial versions, and source-qualified package IDs.
#[cfg(test)]
fn selected_package_names_from_selection(selection: &ResolvedCargoSelection) -> Option<String> {
    let mut names = selection
        .packages
        .iter()
        .map(|package| package.name.as_str())
        .filter(|name| !name.is_empty())
        .collect::<Vec<_>>();
    names.sort_unstable();
    names.dedup();
    (!names.is_empty()).then(|| names.join(","))
}

/// Preserve Cargo's source-qualified package IDs alongside display names for
/// proof-inventory authentication. Names alone are never an authority boundary:
/// one graph can contain several versions or sources with the same name.
fn selected_package_map_from_selection(
    selection: &ResolvedCargoSelection,
) -> BTreeMap<String, String> {
    selection.packages.iter().map(|package| (package.id.clone(), package.name.clone())).collect()
}

fn child_status_code(status: &ExitStatus) -> i32 {
    status.code().unwrap_or_else(|| child_signal_exit_code(status).map(i32::from).unwrap_or(1))
}

fn child_signal_exit_code(status: &ExitStatus) -> Option<u8> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;

        status.signal().map(|signal| 128_i32.saturating_add(signal).min(u8::MAX.into()) as u8)
    }

    #[cfg(not(unix))]
    {
        let _ = status;
        None
    }
}

pub(super) struct LiveReportConsumerInput<'a> {
    pub(super) crate_mode: bool,
    pub(super) compiler_exit: i32,
    pub(super) compiler_signal_exit: Option<u8>,
    pub(super) cargo_proof_inventory: Option<&'a trust_types::CargoProofInventoryReport>,
    pub(super) coverage: Option<&'a trust_types::VerificationCoverage>,
    pub(super) missing_target_coverage: &'a [CargoTargetIdentity],
    pub(super) raw_terminal_inventory_complete: bool,
    pub(super) compiled_targets: &'a BTreeSet<CargoTargetIdentity>,
    pub(super) observed_proof_targets: &'a BTreeSet<CargoTargetIdentity>,
    pub(super) completed_proof_targets: &'a BTreeSet<CargoTargetIdentity>,
    pub(super) coverage_proof_targets: &'a BTreeSet<CargoTargetIdentity>,
}

pub(super) fn live_report_consumer_rejection(input: LiveReportConsumerInput<'_>) -> Option<String> {
    let LiveReportConsumerInput {
        crate_mode,
        compiler_exit,
        compiler_signal_exit,
        cargo_proof_inventory,
        coverage,
        missing_target_coverage,
        raw_terminal_inventory_complete,
        compiled_targets,
        observed_proof_targets,
        completed_proof_targets,
        coverage_proof_targets,
    } = input;
    if let Some(signal_exit) = compiler_signal_exit {
        return Some(format!("compiler terminated by signal (shell status {signal_exit})"));
    }
    if !matches!(compiler_exit, 0 | 1) {
        return Some(format!("compiler terminated abnormally with status {compiler_exit}"));
    }

    let active_exclusions = cargo_active_exclusion_labels(cargo_proof_inventory);
    if !active_exclusions.is_empty() {
        return Some(format!(
            "Cargo proof frontier excluded {} active Unit(s): {}",
            active_exclusions.len(),
            active_exclusions.join("; "),
        ));
    }

    let Some(coverage) = coverage else {
        return Some("authenticated coverage inventory was absent".to_string());
    };
    if !coverage.coverage_complete || coverage.processed != coverage.eligible {
        return Some(format!(
            "authenticated coverage inventory was incomplete ({} of {} functions processed)",
            coverage.processed, coverage.eligible
        ));
    }
    if !missing_target_coverage.is_empty() {
        return Some(
            "one or more completed compiler targets lacked coverage inventory".to_string(),
        );
    }

    if !crate_mode {
        return (!raw_terminal_inventory_complete).then(|| {
            "direct compiler stream lacked one complete authenticated terminal inventory"
                .to_string()
        });
    }

    if completed_proof_targets.is_empty() {
        return Some("Cargo stream lacked a completed proof-target inventory".to_string());
    }
    if observed_proof_targets != completed_proof_targets {
        return Some(
            "observed Cargo proof targets did not exactly equal completed compiler targets"
                .to_string(),
        );
    }
    if coverage_proof_targets != completed_proof_targets {
        return Some(
            "Cargo coverage targets did not exactly equal completed compiler targets".to_string(),
        );
    }
    if !compiled_targets.is_subset(completed_proof_targets) {
        return Some(
            "Cargo artifact targets were not all covered by terminal compiler inventories"
                .to_string(),
        );
    }
    None
}

pub(crate) fn run_compiler(mut run: CompilerRun<'_>) -> ExitCode {
    let export = if let Some(directory) = run.dump_verifier_inputs {
        if !run.cmd_args.first().is_some_and(|p| is_cargo_program(p))
            || run.cmd_args.get(1).is_none_or(|verb| verb != "check")
        {
            report_setup_failure(
                &mut run.diagnostic_observer,
                format_args!("targo trust: --dump-verifier-inputs requires a normal Cargo check"),
            );
            return ExitCode::from(2);
        }
        match crate::verifier_input_export::ExportRun::create(
            directory,
            run.rustc_path,
            run.cmd_args,
        ) {
            Ok(export) => Some(export),
            Err(error) => {
                report_setup_failure(
                    &mut run.diagnostic_observer,
                    format_args!(
                        "targo trust: could not create fresh verifier input export: {error}"
                    ),
                );
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    let mut observer = run.diagnostic_observer.take();
    let status = {
        let mut forward = |diagnostics: &CompilerRunDiagnostics| {
            if let Some(observer) = observer.as_mut() {
                observer(diagnostics);
            }
        };
        run_compiler_with_export(
            CompilerRun {
                cmd_args: run.cmd_args,
                rustc_path: run.rustc_path,
                config: run.config,
                selected_codegen_backend: run.selected_codegen_backend,
                supports_json_transport: run.supports_json_transport,
                strict_artifact_policy: run.strict_artifact_policy,
                strict_result_gate: run.strict_result_gate,
                certify_gate: run.certify_gate,
                allow_l0_gaps: run.allow_l0_gaps,
                memory_safe_policy: run.memory_safe_policy,
                survey: run.survey,
                hardened: run.hardened,
                trust_profile: run.trust_profile,
                spec_emit_dir: run.spec_emit_dir,
                dump_verifier_inputs: run.dump_verifier_inputs,
                format: run.format,
                report_dir: run.report_dir,
                unsafe_memory_report: run.unsafe_memory_report,
                live_report_consumer: run
                    .live_report_consumer
                    .as_mut()
                    .map(|consumer| &mut **consumer as _),
                diagnostic_observer: Some(&mut forward),
                render_output: run.render_output,
                ephemeral_single_file_output: run.ephemeral_single_file_output,
                test_target_panics: run.test_target_panics,
                agent_delta: run.agent_delta,
            },
            export.as_ref(),
        )
    };
    if let Some(export) = export {
        use sha2::{Digest, Sha256};
        if let Err(error) = export
            .finish(status == ExitCode::SUCCESS, |bytes| format!("{:x}", Sha256::digest(bytes)))
        {
            report_artifact_failure(
                &mut observer,
                format_args!(
                    "targo trust: verifier input export was incomplete at `{}`: {error}; verification result is unchanged",
                    export.directory().display()
                ),
            );
            // Preserve the verifier's actual failure. A successful check whose requested
            // export failed is an output error, never a successful capture claim.
            if status == ExitCode::SUCCESS {
                return ExitCode::from(2);
            }
        } else {
            eprintln!(
                "targo trust: verifier input census: {}/verifier-inputs.json (observational only; absent entries are not captures)",
                export.directory().display()
            );
        }
    }
    status
}

fn run_compiler_with_export(
    run: CompilerRun<'_>,
    export: Option<&crate::verifier_input_export::ExportRun>,
) -> ExitCode {
    let CompilerRun {
        cmd_args,
        rustc_path,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        strict_result_gate,
        certify_gate,
        allow_l0_gaps,
        memory_safe_policy,
        survey,
        hardened,
        trust_profile,
        spec_emit_dir,
        dump_verifier_inputs: _,
        format,
        report_dir,
        unsafe_memory_report,
        mut live_report_consumer,
        mut diagnostic_observer,
        render_output,
        ephemeral_single_file_output,
        test_target_panics,
        agent_delta,
    } = run;

    if cmd_args.is_empty() {
        report_setup_failure(
            &mut diagnostic_observer,
            format_args!("targo trust: internal error: empty command"),
        );
        return ExitCode::from(2);
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    // Determinism plan §3.6: the bounds the compiler will run under — the
    // workspace root's `[trust]` effort and backstop, and the worker-thread
    // count `--worker-threads` passes (recorded, not in the id).
    let budget_profile = crate::determinism_report::budget_profile(config);
    let crate_mode = is_cargo_program(program);
    let cargo_test_mode = crate_mode && args.first().is_some_and(|arg| arg == "test");
    let cargo_test_compile_only =
        cargo_test_mode && cargo_arg_before_passthrough(args, |arg| arg == "--no-run");
    if cargo_test_mode {
        if let Some(report_dir) = report_dir {
            if let Err(error) = crate::report::invalidate_report_bundle(Path::new(report_dir)) {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!(
                        "targo trust: could not invalidate the previous certified-test report bundle: {error}"
                    ),
                );
                return ExitCode::from(2);
            }
        }
    }
    let cargo_execution_mode =
        crate_mode && args.first().is_some_and(|arg| matches!(arg.as_str(), "test" | "bench"));
    if crate_mode {
        if let Some(error) = cargo_compiler_override_diagnostic(args) {
            report_setup_failure(&mut diagnostic_observer, format_args!("targo trust: {error}"));
            return ExitCode::from(2);
        }
    }
    if crate_mode && !supports_json_transport {
        report_setup_failure(
            &mut diagnostic_observer,
            format_args!(
                "targo trust: selected compiler lacks the structured Trust transport required for evidence-grade Cargo verification"
            ),
        );
        return ExitCode::from(2);
    }
    if cargo_test_mode && !cargo_test_has_explicit_target_selector(args) {
        eprintln!(
            "targo trust: note: the retained queue preserves Cargo's default non-doc compile coverage and executes its prepared ordinary test targets after proof qualification; doctests require a separate authenticated rustdoc lane"
        );
    }
    let verification_session = match VerificationSession::create() {
        Ok(session) => session.with_proof_store(),
        Err(error) => {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: could not create verification freshness token: {error}"),
            );
            return ExitCode::from(2);
        }
    };
    if let Some(export) = export {
        if let Err(error) =
            export.bind(verification_session.artifact_root(), &verification_session.id)
        {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!(
                    "targo trust: could not bind verifier input export to this session: {error}"
                ),
            );
            return ExitCode::from(2);
        }
    }
    let hardened_profile = hardened_profile_name(hardened, trust_profile).map(str::to_string);
    let requirements = match requirement_flags_for_run(
        config,
        memory_safe_policy,
        survey,
        certify_gate,
        allow_l0_gaps,
        hardened_profile.as_deref(),
    ) {
        Ok(requirements) => requirements,
        Err(error) => {
            report_setup_failure(&mut diagnostic_observer, format_args!("targo trust: {error}"));
            return ExitCode::from(2);
        }
    };
    let controls = VerificationControls {
        policy: TrustPolicySelection::from_lane_flags(memory_safe_policy, survey, certify_gate),
        budget: &budget_profile,
        hardened_profile: hardened_profile.as_deref(),
        verification_session: &verification_session.id,
        proof_artifact_root: verification_session.artifact_root(),
        spec_emit_dir,
    };
    let mut effective_args = if crate_mode {
        let normalized = if cargo_test_mode && !cargo_test_compile_only {
            cargo_test_retained_args(args)
        } else if cargo_test_mode {
            cargo_test_compile_only_args(args)
        } else {
            cargo_args_with_proof_message_format(args)
        };
        match normalized {
            Ok(args) => args,
            Err(error) => {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!(
                        "targo trust: could not establish Cargo proof execution plan: {error}"
                    ),
                );
                return ExitCode::from(2);
            }
        }
    } else {
        args.to_vec()
    };
    let retained_test_queue = crate_mode && cargo_test_mode && !cargo_test_compile_only;
    if !crate_mode {
        if let Err(error) = append_verification_control_args(&mut effective_args, &controls) {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: could not configure verifier options: {error}"),
            );
            return ExitCode::from(2);
        }
        // The adopted project requirements are merged last, mirroring the
        // crate-mode lane (verified_lane_flags).
        requirements.apply_to_args(&mut effective_args);
        // Trust (v6/D1): a direct trustc invocation takes the typed sink on
        // argv; this is deliberately outside `verification_control_options`,
        // whose output must stay inside the graph-wide host-policy protocol.
        if let Some(dir) = controls.spec_emit_dir {
            effective_args.push("-Z".to_string());
            effective_args.push(format!("trust-dump=spec-clean:{}", dir.display()));
        }
    }
    let _ephemeral_output =
        match prepare_ephemeral_single_file_output(args, ephemeral_single_file_output) {
            Ok(output) => output,
            Err(error) => {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!(
                        "targo trust: could not prepare temporary single-file output: {error}"
                    ),
                );
                return ExitCode::from(2);
            }
        };
    let start = Instant::now();

    // For targo-based invocations, pin RUSTC to the discovered Trust
    // toolchain; verifier policy (config-derived plus project requirements)
    // rides in the rustflags environment assembled below.
    let cargo_selection = if crate_mode {
        match resolve_cargo_selection_for_compiler(args, rustc_path, program) {
            Ok(selection) => Some(selection),
            Err(error) => {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!(
                        "targo trust: could not resolve canonical Cargo package selection: {error}"
                    ),
                );
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    let selected_cargo_packages = cargo_selection.as_ref().map(selected_package_map_from_selection);
    // T7c: from here on a selected package's records are this run's or
    // absent, never an earlier run's that a run which stops before it writes
    // them (trustd not established, a compile that published nothing) would
    // leave in place looking like its own. Every exit above is exit 2 and
    // removes nothing (`crate::package_record::remove_records`).
    if let Some(selection) =
        cargo_selection.as_ref().filter(|_| args.first().is_some_and(|arg| arg == "check"))
    {
        let target_dir = cargo_target_dir(args, Some(&selection.target_directory));
        let selected = selection.packages.iter().map(|package| package.name.clone()).collect();
        if let Err(error) = crate::package_record::remove_records(&target_dir, &selected) {
            eprintln!(
                "targo trust: warning: could not remove the selected packages' earlier records \
                 under `{}`: {error}; a record there may be an earlier run's",
                target_dir.join("trust").display()
            );
        }
    }
    let mut cmd = if let Some(selection) = cargo_selection.as_ref() {
        match configured_verified_cargo_child(
            program,
            &effective_args,
            args,
            rustc_path,
            config,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
            &controls,
            &requirements,
            selection,
            cargo_test_mode,
            None,
        ) {
            Ok(command) => command,
            Err(error) => {
                observe_compiler_errors(
                    &mut diagnostic_observer,
                    &[CompilerDiagnostic {
                        level: "error".into(),
                        message: format!("could not configure Cargo verifier options: {error}"),
                    }],
                );
                return error.report("could not configure Cargo verifier options");
            }
        }
    } else {
        let mut command = Command::new(program);
        command.args(&effective_args);
        scrub_proof_compiler_authority_env(&mut command);
        scrub_legacy_verifier_env(&mut command);
        apply_targo_test_monitor_session(&mut command, false, &verification_session.id);
        apply_native_runtime_env(&mut command, rustc_path);
        command
    };
    if cargo_test_mode && !cargo_test_compile_only {
        cmd.env(
            trust_test_execution::EXPORT_ENV,
            verification_session.artifact_root().join("prepared-tests.json"),
        );
        cmd.env(trust_test_execution::EXPORT_SESSION_ENV, &verification_session.id);
    }
    cmd.stderr(Stdio::piped());
    if crate_mode {
        cmd.stdout(Stdio::piped());
    }

    let mut process = match RunChild::spawn(
        &mut cmd,
        retained_test_queue.then_some(verification_session.id.as_str()),
        CompilerProcessBounds::from_backstop(config.backstop),
    ) {
        Ok(process) => process,
        Err(error) => {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: failed to spawn `{program}`: {error}"),
            );
            return ExitCode::from(error.exit_code());
        }
    };

    let cargo_stdout = if crate_mode {
        let Some(stdout) = process.child_mut().stdout.take() else {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: canonical Targo stdout pipe was not available"),
            );
            return ExitCode::from(2);
        };
        let selected = selected_cargo_packages
            .as_ref()
            .expect("crate mode has canonical package selection")
            .clone();
        Some(spawn_cargo_stdout_parser(
            stdout,
            process.progress(),
            selected,
            verification_session.id.clone(),
            strict_artifact_policy,
            cargo_execution_mode,
            cargo_test_mode && !cargo_test_compile_only,
        ))
    } else {
        None
    };

    let Some(stderr) = process.child_mut().stderr.take() else {
        report_setup_failure(
            &mut diagnostic_observer,
            format_args!("targo trust: compiler stderr pipe was not available"),
        );
        return ExitCode::from(2);
    };
    // Drain both compiler pipes concurrently with the lifecycle wait. Besides
    // preventing pipe-buffer deadlock, this is what makes the portable
    // try_wait deadline reachable on platforms without the Unix watchdog.
    let stderr_output = spawn_compiler_stderr_parser(
        stderr,
        process.progress(),
        crate_mode,
        render_output == ReportRendering::Stdout,
        supports_json_transport,
        verification_session.id.clone(),
        strict_artifact_policy,
    );

    let compile_completion = match process.compile_completion() {
        Ok(completion) => completion,
        Err(ChildSetupError::CouldNotRun(error)) => {
            observe_compiler_errors(
                &mut diagnostic_observer,
                &[CompilerDiagnostic {
                    level: "error".into(),
                    message: format!("compiler process backstop: {error}"),
                }],
            );
            return backstop_ended_the_compiler(&error, config.backstop);
        }
        Err(error) => {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: failed to establish compiler completion: {error}"),
            );
            return ExitCode::from(error.exit_code());
        }
    };
    let mut execution_status: Option<ExitStatus> = None;

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics;
    let mut cached_obligations = 0usize;
    let mut coverage_rows = Vec::new();
    let mut compiler_memory_observations = Vec::new();
    let mut native_admission_observations = Vec::new();
    let mut native_admission_problems = Vec::new();
    let mut coverage_dropped = Vec::new();
    let mut coverage_proof_targets = BTreeSet::new();
    let mut observed_proof_targets = BTreeSet::new();
    let mut completed_proof_targets = BTreeSet::new();
    let mut compiled_targets = BTreeSet::new();
    let mut test_executables = BTreeSet::new();
    let mut prepared_tests = None;
    // Disclosure for the records and the changed-only view only
    // (`crate::obligations`): the compile errors Cargo reported.
    let mut compile_errors = Vec::new();
    // Disclosure only, likewise: the island rows each unit published.
    let mut clean_island_rows = BTreeMap::new();
    let mut cargo_proof_inventory = None;
    // Successful-child transport defects are setup/evidence failures, but
    // they must still flow through the canonical failed-report path. Returning
    // here would suppress the very diagnostic artifact callers requested and
    // make an unauthenticated empty stream observationally indistinguishable
    // from a report-rendering failure.
    let mut cargo_evidence_integrity_errors = Vec::new();

    let parsed_stderr = match receive_compiler_output(stderr_output, "compiler stderr") {
        Ok(parsed) => parsed,
        Err(error) => {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: invalid compiler stderr channel: {error}"),
            );
            return ExitCode::from(2);
        }
    };
    let raw_terminal_inventory_complete =
        !crate_mode && parsed_stderr.raw_terminal_inventory_complete();
    if crate_mode {
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
    } else {
        let ParsedCompilerOutput {
            verification_results: parsed_results,
            compiler_diagnostics: parsed_diagnostics,
            cached_obligations: parsed_cached,
            coverage_rows: parsed_coverage,
            dropped_coverage: parsed_dropped,
            ..
        } = parsed_stderr;
        verification_results = parsed_results;
        compiler_diagnostics = parsed_diagnostics;
        cached_obligations = parsed_cached;
        compiler_memory_observations = parsed_coverage
            .iter()
            .map(crate::compiler_memory::CompilerMemoryObservation::direct)
            .collect();
        coverage_rows = parsed_coverage;
        coverage_dropped = parsed_dropped;
    }

    observe_compiler_errors(&mut diagnostic_observer, &compiler_diagnostics);

    if let Some(channel) = cargo_stdout {
        let evidence = match receive_compiler_output(channel, "canonical Cargo stdout") {
            Ok(evidence) => evidence,
            Err(error) => {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!("targo trust: invalid canonical Cargo evidence channel: {error}"),
                );
                return ExitCode::from(2);
            }
        };
        if compile_completion.success() {
            let selected = selected_cargo_packages
                .as_ref()
                .expect("crate mode has canonical package selection");
            if let Err(error) =
                evidence.require_successful_selected_roots(selected, strict_artifact_policy)
            {
                eprintln!("targo trust: invalid successful Cargo proof inventory: {error}");
                cargo_evidence_integrity_errors
                    .push(format!("invalid successful Cargo proof inventory: {error}"));
            }
        }
        cargo_proof_inventory = evidence.declared_inventory;
        let parsed = evidence.parsed.require_structured_json_transport(true);
        verification_results = parsed.verification_results;
        observe_compiler_errors(&mut diagnostic_observer, &parsed.compiler_diagnostics);
        compiler_diagnostics.extend(parsed.compiler_diagnostics);
        cached_obligations = parsed.cached_obligations;
        compiler_memory_observations = parsed.compiler_memory_observations;
        native_admission_observations = parsed.native_admission_observations;
        native_admission_problems = parsed.native_admission_problems;
        coverage_rows = parsed.coverage_rows;
        coverage_dropped = parsed.dropped_coverage;
        coverage_proof_targets = parsed.coverage_proof_targets;
        observed_proof_targets = parsed.observed_proof_targets;
        completed_proof_targets = parsed.completed_proof_targets;
        compiled_targets = evidence.compiled_targets;
        test_executables = evidence.test_executables;
        prepared_tests = evidence.prepared_tests;
        compile_errors = evidence.compile_errors;
        clean_island_rows = evidence.clean_island_rows;
        if let Err(error) = compile_completion.require_receipt(prepared_tests.as_ref()) {
            cargo_evidence_integrity_errors.push(error);
        }
    }

    // Preserve the exact authenticated compiler vector before applying the one
    // publication normalization.  The normalized vector can only downgrade a
    // proof label or elide a redundant diagnostic alias; it never manufactures
    // a Targo-owned Proved row.  Live publication authority later recomputes
    // this projection from the compiler vector before it mints any receipts.
    //
    // This clone is LOAD-BEARING and must stay a clone: `verification_results`
    // is normalized IN PLACE two statements below, so a borrow of it would hand
    // `capture_authenticated_projection` the already-normalized rows, and the
    // drift check would compare the publication vector against itself and pass
    // unconditionally.  What was reduced instead is its LIFETIME: it is moved
    // into that constructor at its last use rather than living to the end of
    // this function.
    let authenticated_compiler_results = verification_results.clone();
    // T9: every function the compiler verified, with its source digest, read
    // before the normalization below elides the inventory-only rows: a
    // function that published no obligation is still a function.
    let function_inventory =
        crate::obligations::FunctionInventory::of_rows(&authenticated_compiler_results);
    let zero_obligation_functions =
        crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
    // Trust (CB4): the libtest harness bodies the compiler excluded, read from
    // their exact rows before the normalization below elides those rows. Same
    // derivation the live authority repeats from the same vector.
    let test_harness_exclusions =
        crate::types::authenticated_test_harness_exclusions(&authenticated_compiler_results);
    // Trust (#220): the boundary this pass applies used to be discarded here.
    // It is the ONLY point at which a demoted-then-elided row is still
    // countable, so it is captured and carried into the report for disclosure.
    let publication_boundary = crate::types::normalize_authenticated_results_for_publication(
        &mut verification_results,
        Some(verification_session.artifact_root()),
    );

    // `--test-target-panics`. Applied HERE — after the publication
    // normalization, before any receipt is minted — so that normalization sees
    // exactly the rows it sees today (its twin-subsumption and demotion passes
    // are untouched) and the live authority is minted over the rows this run
    // actually publishes. `capture_authenticated_projection` recomputes the
    // same projection under the same policy, so the receipt still binds.
    // Under `TestTargetPanicPolicy::Strict` this is a no-op returning 0.
    let test_target_panics_reclassified =
        crate::test_target_panics::apply(&mut verification_results, test_target_panics);
    if test_target_panics_reclassified > 0 {
        eprintln!(
            "targo trust: {} refuted panic-class obligation(s) in cargo test targets recorded as \
             runtime-checked conditions by `{}={}`; none of them is proved",
            test_target_panics_reclassified,
            crate::test_target_panics::FLAG,
            test_target_panics.as_str(),
        );
    }

    persist_verification_snapshot(args, cargo_selection.as_ref(), &authenticated_compiler_results);

    let phase_a_status = compile_completion.code();
    let phase_a_success = compile_completion.success();
    let mut post_phase_a_orchestration_error: Option<ChildSetupError> = None;
    let test_execution = cargo_test_mode.then(|| CertifiedTestExecutionReport {
        schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
        completion_scope: if compile_completion.is_checkpoint() {
            CertifiedTestExecutionCompletionScope::RetainedCompileCheckpointAndChildExitV1
        } else {
            CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1
        },
        requested: true,
        scope: if compile_completion.is_checkpoint() {
            trust_types::CERTIFIED_RETAINED_TEST_EXECUTION_SCOPE.to_string()
        } else {
            trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string()
        },
        compile_only: cargo_test_compile_only,
        phase_a_status,
        phase_a_success,
        phase_b_state: if cargo_test_compile_only {
            CertifiedTestExecutionPhaseState::NotRequested
        } else {
            CertifiedTestExecutionPhaseState::Blocked
        },
        blocker: None,
        phase_b_exit: None,
        authorized_executables: Vec::new(),
        authorized_inventory_sha256: None,
        target_directory: None,
    });

    if cargo_test_mode {
        for executable in &test_executables {
            compiler_diagnostics.push(CompilerDiagnostic {
                level: "note".to_string(),
                message: format!(
                    "targo trust: certified test execution inventory target={} path={} phase_a_sha256={}",
                    executable.target.report_label(),
                    executable.path.display(),
                    executable.phase_a_sha256,
                ),
            });
        }
        if cargo_test_compile_only {
            compiler_diagnostics.push(CompilerDiagnostic {
                level: "note".to_string(),
                message: "targo trust: certified test execution state=compile-only (`--no-run`); no test process ran, so no installed runtime monitor could be reached"
                    .to_string(),
            });
        }
    }

    let mut compiler_exit = match &post_phase_a_orchestration_error {
        Some(error) => i32::from(error.exit_code()),
        None => compile_completion.code(),
    };
    let mut compiler_signal_exit = post_phase_a_orchestration_error
        .is_none()
        .then(|| compile_completion.signal_exit())
        .flatten();
    let duration_ms = start.elapsed().as_millis() as u64;
    if let Some(profile) = hardened_profile.as_deref() {
        let message = format!(
            "targo trust: hardened profile `{profile}` enabled; `--no-hardened` turns it off \
             unless the project's Cargo configuration requires it"
        );
        if !compiler_diagnostics.iter().any(|diagnostic| diagnostic.message == message) {
            compiler_diagnostics.push(CompilerDiagnostic { level: "note".into(), message });
        }
    }

    // Count verification outcomes into the disjoint Stage-2 partition:
    // proved / failed / runtime_checked, plus a three-way split of the
    // inconclusive rows into assumed (`assumption:*`), mandated (the compiler's
    // design_mandate bit), and genuine unknown. Defective assumption rows
    // (claiming proof) are fail-closed to unknown and surfaced as transport
    // defects on stderr.
    let (counts, transport_defects) = partition_outcome_counts(&verification_results);
    for defect in &transport_defects {
        eprintln!("targo trust: {defect}");
    }
    let OutcomeCounts {
        total,
        proved,
        failed,
        unknown,
        runtime_checked,
        assumed,
        mandated,
        contract_panics,
        // Trust (CB4): exact exclusion rows were elided before this partition;
        // the authenticated inventory is added to the gate counts below.
        excluded: _,
    } = counts;

    // The exit-code gate. The advisory lane (the ramp) exits 0 on a conditional
    // pass: no refutation, and every non-proved row either an EXPLICIT ledger
    // entry or — since 2026-09-07 — a genuine unknown, all of them carried in
    // the decision. The canonical strict lane uses the historical
    // `compiler_verification_success` predicate and keeps an unknown fatal.
    let lane = if certify_gate {
        GateLane::Certify
    } else if memory_safe_policy {
        GateLane::MemorySafe
    } else if strict_result_gate {
        GateLane::Strict
    } else {
        GateLane::Advisory
    };
    let gate_counts = if lane == GateLane::MemorySafe {
        let (gate_counts, defects) = memory_safe_gate_counts(&verification_results, counts);
        for defect in defects {
            eprintln!("targo trust: {defect}");
        }
        gate_counts
    } else if lane == GateLane::Strict {
        // The strict lane's conditional pass rests on the compiler's STRICT
        // policy having produced its `assumed` rows; see `strict_gate_counts`.
        let (gate_counts, defects) = strict_gate_counts(&verification_results, counts);
        for defect in defects {
            eprintln!("targo trust: {defect}");
        }
        gate_counts
    } else {
        counts
    };
    // Trust (CB4): the excluded libtest harness bodies join the gate counts in
    // their own bucket, outside `total`: disclosed, never proof, never a
    // condition. See `OutcomeCounts::excluded`.
    let gate_counts = OutcomeCounts {
        excluded: gate_counts.excluded.saturating_add(test_harness_exclusions.len()),
        ..gate_counts
    };
    // Trust (assertion-grade coverage, roadmap §4.1): the compiler's
    // `coverage_summary` row(s). Any accounting mismatch (`processed != eligible`)
    // means whole-crate coverage was not established — a FAIL-CLOSED condition like an unknown,
    // not a warning: the gate is capped at Inconclusive (never a passing gate).
    // `None` is coverage-UNKNOWN. Current strict compiler policy promises the
    // row, so absence is inconclusive there; explicit advisory/survey lanes
    // retain compatibility with older compilers and report the unknown.
    let coverage_overflowed = coverage_accounting_overflowed(&coverage_rows);
    // Trust (CB4): each excluded body is an eligible body the compiler
    // PROCESSED (its one envelope is the exclusion row), so it is inside
    // `processed`; `excluded` only splits it out for the reader.
    let coverage = aggregate_coverage(&coverage_rows).map(|mut coverage| {
        coverage.excluded = test_harness_exclusions.len();
        coverage
    });
    let missing_target_coverage =
        completed_proof_targets.difference(&coverage_proof_targets).cloned().collect::<Vec<_>>();
    if let Some(cov) = coverage.filter(|cov| !cov.coverage_complete) {
        if !coverage_overflowed && cov.processed < cov.eligible {
            eprintln!(
                "targo trust: coverage shortfall: {} function(s) were never verified \
                 ({} of {} eligible function bodies processed) — the verification report \
                 does NOT cover the whole crate; fail-closed: this run cannot pass",
                cov.eligible - cov.processed,
                cov.processed,
                cov.eligible,
            );
        } else {
            eprintln!(
                "targo trust: malformed coverage accounting: {} processed function bodies \
                 were reported for {} eligible bodies — proof completeness cannot be \
                 established; fail-closed: this run cannot pass",
                cov.processed, cov.eligible,
            );
        }
    }
    let require_coverage = strict_artifact_policy;
    if require_coverage && (coverage.is_none() || !missing_target_coverage.is_empty()) {
        if missing_target_coverage.is_empty() {
            eprintln!(
                "targo trust: missing coverage_summary transport — strict proof completeness cannot be established; fail-closed"
            );
        } else {
            let targets = missing_target_coverage
                .iter()
                .map(CargoTargetIdentity::report_label)
                .collect::<Vec<_>>()
                .join(", ");
            eprintln!(
                "targo trust: missing coverage_summary transport for completed target(s): {targets} — strict proof completeness cannot be established; fail-closed"
            );
        }
    }
    let excluded_functions = test_harness_exclusions
        .iter()
        .map(|exclusion| exclusion.function.clone())
        .collect::<Vec<_>>();
    let gate_decision = evaluate_run_gate(
        lane,
        compiler_exit,
        gate_counts,
        coverage.as_ref(),
        !missing_target_coverage.is_empty(),
        require_coverage,
        &zero_obligation_functions,
        &excluded_functions,
    );
    // A run with no authenticated evidence that verification executed is a
    // hard setup error, never a plausible zero-obligation report. Coverage
    // rows reaching this point have already passed raw/Cargo authentication.
    let missing_trust_json = missing_trust_json_diagnostic(
        crate_mode,
        &verification_results,
        &completed_proof_targets,
        !coverage_rows.is_empty(),
    );

    // Trust (assumption ledger): compute the dep-TCB entries BEFORE the report
    // literal so the crate-scope assumptions land in report.json (the stderr
    // ledger rendering below derives from the same set's line renderer).
    let dep_assumptions = if crate_mode {
        crate::dep_tcb::dep_tcb_assumption_entries(cargo_proof_inventory.as_ref())
    } else {
        Vec::new()
    };
    let canonical_cargo_proof_inventory = if crate_mode {
        match cargo_proof_inventory_report(
            cargo_proof_inventory.as_ref(),
            &completed_proof_targets,
            &coverage_proof_targets,
        ) {
            Ok(report) => report,
            Err(error) => {
                eprintln!("targo trust: invalid Cargo proof report inventory: {error}");
                cargo_evidence_integrity_errors
                    .push(format!("invalid Cargo proof report inventory: {error}"));
                None
            }
        }
    } else {
        None
    };
    // Only exclusions NOT admitted to the dependency-TCB ledger fail the gate.
    // A ledger-admitted third-party dep (dependency-policy / build-script) is a
    // recorded trust assumption (see `dep_assumptions` above), not a proof gap;
    // an unresolved exclusion still fails closed. This keeps the gate and the
    // dep-TCB admission ledger in agreement.
    let active_cargo_exclusions =
        cargo_gate_failing_exclusion_labels(canonical_cargo_proof_inventory.as_ref());
    let cargo_exclusion_gate_failure = !active_cargo_exclusions.is_empty();
    if cargo_exclusion_gate_failure {
        eprintln!(
            "targo trust: Cargo proof frontier excluded {} active Unit(s) outside the dependency-TCB ledger; whole-crate proof is incomplete and the verification gate cannot pass: {}",
            active_cargo_exclusions.len(),
            active_cargo_exclusions.join("; "),
        );
    }
    for error in &cargo_evidence_integrity_errors {
        compiler_diagnostics
            .push(CompilerDiagnostic { level: "error".into(), message: error.clone() });
    }
    // Trust (a trustd outage is a SETUP failure, not N unknowns): a row the
    // compiler minted because the configured memory authority could not admit
    // the function was never dispatched to any solver. Counting it as
    // `unknown` makes an infrastructure outage indistinguishable from a
    // modelling gap in the census — on 2026-09-19 a 4h44m gate over ay
    // reported 282,786 of these in its last eight seconds after a test stub
    // unlinked the live daemon's socket, and the run was read for two days as
    // "the verifier does not support 75% of what it is asked". The gate did
    // exit nonzero, but for the wrong stated reason. Recognise the closed
    // vocabulary the compiler mints (never free text) and name the outage once.
    //
    // Determinism plan §3.2/§3.7: the same holds for a SOLVER the memory
    // authority refused to spawn (the router stamps `admission-refused` on that
    // row). Either way the obligation's stop cause is `admission-refused` and
    // the unit could not run: it is never an Unknown in a count, and the run
    // exits 3 (COULD NOT RUN) through its outcome below, not 2 (T7b).
    let admission_refused = |row: &VerificationResult| {
        crate::determinism_report::row_stop_cause(row)
            == trust_types::determinism::StopCause::AdmissionRefused
    };
    let memory_admission_prefix = trust_types::VcKind::memory_admission_message_prefix();
    let memory_admission_failures =
        verification_results.iter().filter(|row| admission_refused(row)).count();
    if memory_admission_failures > 0 {
        let first = verification_results
            .iter()
            .find(|row| admission_refused(row))
            .map(|row| {
                row.message
                    .strip_prefix(memory_admission_prefix.as_str())
                    .map(str::to_string)
                    .or_else(|| row.reason.clone())
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        compiler_diagnostics.push(CompilerDiagnostic {
            level: "error".into(),
            message: format!(
                "targo trust: memory authority unreachable: {memory_admission_failures} \
                 obligation(s) were never dispatched to a solver, so this run is not a \
                 verification verdict; first: {first}"
            ),
        });
    }
    let evidence_setup_failed =
        missing_trust_json.is_some() || !cargo_evidence_integrity_errors.is_empty();
    let base_success = gate_decision.is_success()
        && !cargo_exclusion_gate_failure
        && post_phase_a_orchestration_error.is_none();
    let report_subject = if crate_mode {
        cargo_report_subject(&compiled_targets, &observed_proof_targets, &completed_proof_targets)
    } else {
        match single_file_report_subject(cmd_args) {
            Ok(subject) => subject,
            Err(error) => {
                report_setup_failure(
                    &mut diagnostic_observer,
                    format_args!("targo trust: {error}"),
                );
                return ExitCode::from(2);
            }
        }
    };
    // Mint same-process row authority only after the protected compiler/Cargo
    // channels and target-inventory checks.  The constructor independently
    // recomputes the fail-closed publication projection from the exact compiler
    // vector, so an arbitrary post-parse rewrite cannot acquire proof credit.
    // MOVED, not borrowed. This is the last use of the authenticated snapshot,
    // and the constructor consumes it as its own projection buffer, so the
    // second full row vector is released here instead of staying live through
    // the seal and the render below.
    let live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
        &report_subject,
        &verification_session.id,
        authenticated_compiler_results,
        &verification_results,
        Some(verification_session.artifact_root()),
        test_target_panics,
    );
    let noted_stops = crate::determinism_report::noted_stops_with_publication(
        &crate::determinism_report::merged_noted_stops(&coverage_rows),
        &publication_boundary.elided_stops,
        None,
    );
    observe_compiler_errors(&mut diagnostic_observer, &compiler_diagnostics);
    let mut report = VerificationReport {
        report_subject,
        success: base_success,
        exit_code: compiler_exit,
        proved,
        failed,
        unknown,
        runtime_checked,
        assumed,
        mandated,
        contract_panics,
        cached: cached_obligations,
        total,
        results: verification_results,
        publication_boundary: Some(publication_boundary),
        zero_obligation_functions,
        test_harness_exclusions,
        compiler_diagnostics,
        duration_ms,
        config: ReportConfig {
            level: config.level.clone(),
            budget_profile: budget_profile.clone(),
            enabled: config.enabled,
            hardened,
            trust_profile: hardened_profile.clone(),
            project_requirements: config.project_policy.as_ref().and_then(|policy| policy.report()),
        },
        dep_assumptions,
        gate: None,
        // Determinism plan §2: the backstops every compiled unit's ledger saw
        // fire, in a row or not; any makes the unit not reproducible.
        noted_stops,
        coverage,
        coverage_dropped,
        test_execution,
        cargo_proof_inventory: canonical_cargo_proof_inventory,
        proof_artifact_root: Some(verification_session.artifact_root().to_path_buf()),
        live_transport_authority,
    };
    let hardened_gate_failure = report.hardened_proof_gate_failure();
    if let Some(gap) = hardened_gate_failure {
        eprintln!(
            "targo trust: hardened proof evidence gate failed: {}/{} hardened obligations have publishable native proof evidence",
            gap.proof_evidence_entries, gap.hardened_obligations
        );
        report.success = false;
    }
    if evidence_setup_failed {
        report.success = false;
    }

    // Decide the proof-phase status before authorizing execution; the same
    // evaluator later binds the actual test outcome before publication.
    // A missing compiler transport is a setup/evidence failure (2), not an
    // ordinary verification-gate failure (1), even when Cargo itself exited 0.
    //
    // Verification-in-compilation era: a fail-closed verification outcome makes
    // trustc emit hard errors, so Cargo exits 101 even though the run is an
    // ORDINARY verification-gate failure with a full sealed report. The CLI
    // contract (and the e2e corpora that pin it) reserves exit 1 for exactly
    // that case, and passes the compiler's own code through otherwise (genuine
    // compile/setup errors, ICEs). Two conjuncts, both required:
    //  * the verification session CONCLUDED — the authenticated coverage
    //    inventory is present, complete, and covers every completed target. A
    //    compiler that died mid-run (ICE, signal wrapper, genuine compile
    //    error aborting before verification) never completes coverage, so its
    //    own status passes through
    //    (`live_report_consumer_cannot_override_early_proof_followed_by_ice`:
    //    a claimed-proved prefix followed by death must keep the ICE status —
    //    row counting alone cannot see this, because the transport synthesizes
    //    a defect row for the abnormal end and claimed rows are downgraded);
    //  * the outcome partition actually contains a non-proved row (a concluded
    //    run that failed for NON-verification reasons keeps its own status).
    let verification_concluded = missing_target_coverage.is_empty()
        && coverage.as_ref().is_some_and(|coverage| {
            coverage.coverage_complete && coverage.processed == coverage.eligible
        });
    // Determinism plan §2/§4.8 (T7b): a run whose rows are not a measurement —
    // outcome `could-not-run` or `not-reproducible` — exits 3, COULD NOT RUN,
    // when those rows alone failed it: never over a refutation, a failing
    // test, a compile error they do not account for, or a gate a re-run cannot
    // change (see `RunExit::decide`).
    let every_unit_concluded = verification_concluded
        && cargo_proof_inventory
            .as_ref()
            .is_none_or(|inventory| inventory.proof_targets.is_subset(&completed_proof_targets));
    let gate_inputs = RunGateInputs {
        lane,
        decision: gate_decision,
        counts: gate_counts,
        verification_level: &config.level,
        coverage,
        verification_concluded,
        every_unit_concluded,
        hardened_gate_failed: hardened_gate_failure.is_some(),
        evidence_setup_failed,
        cargo_exclusion_gate_failure,
    };
    let mut process_exit = finalize_run_gate(
        &mut report,
        &gate_inputs,
        compiler_exit,
        compiler_signal_exit,
        post_phase_a_orchestration_error.as_ref(),
    );
    // A refused seal must not end the run in SILENCE. Grade every row unproved,
    // rebuild the gate fail-closed, and publish that — the rows, the coverage
    // row, a real `Gate:` line, and a nonzero exit — with the refused
    // precondition named. Nothing here can launder credit: the re-mint refuses
    // outright unless every row is non-favorable, so a fail-closed publication
    // is sealed without the seal ever accepting evidence it refused.
    let mut qualified_test_execution = None;
    if let Err(refusal) = QualifiedTestExecution::seal(&mut report, &verification_session.id)
        .map(|qualification| qualified_test_execution = qualification)
    {
        if !test_qualification::publish_seal_refusal(&mut report, &refusal) {
            return ExitCode::from(2);
        }
        process_exit = ExitCode::from(2);
    }

    let preexecution_diagnostics = report.compiler_diagnostics.len();
    // `targo trust test` is evidence-gated before user code executes. Phase A
    // compiled all non-doc test targets under the unique proof session and the
    // parser authenticated their finite transport. The original child remains
    // alive with its queue and permits. The same frontend proof gate and seal
    // must pass before that queue receives its one-shot execution grant. Targo
    // copies each byte-identical authorized test artifact into an authenticated
    // execution snapshot: Linux launches a sealed anonymous image by handle;
    // macOS authenticates a private signed snapshot and the suspended live
    // process's CDHash before resume. Unsupported platforms and missing or
    // invalid retained companions fail closed. There is no second execution
    // process or unauthenticated pathname fallback.
    // The plan native Targo was granted, once a harness started: where each
    // harness's per-case results are (`crate::test_results`).
    let mut executed_test_plan: Option<trust_test_execution::PreparedTests> = None;
    let test_execution_refused = post_phase_a_orchestration_error.is_some();
    if cargo_test_mode && !cargo_test_compile_only && post_phase_a_orchestration_error.is_none() {
        if qualified_test_execution.is_none() {
            let blocker = format!(
                "current frontend proof qualification did not pass (gate={}, exit={:?})",
                report.gate.as_ref().map_or("unavailable", |gate| gate.decision.as_str()),
                process_exit,
            );
            eprintln!(
                "targo trust: refusing to execute Cargo tests before authenticated build evidence is complete: {blocker}"
            );
            report.compiler_diagnostics.push(CompilerDiagnostic {
                level: "error".to_string(),
                message: format!(
                    "targo trust: certified test execution state=blocked-before-execution: {blocker}"
                ),
            });
            if let Some(execution) = report.test_execution.as_mut() {
                execution.phase_b_state = CertifiedTestExecutionPhaseState::Blocked;
                execution.blocker = Some(blocker);
            }
        } else {
            let selection =
                cargo_selection.as_ref().expect("Cargo test mode has canonical package selection");
            // `targo metadata` reports its own effective target directory but
            // does not consume the build command's `--target-dir`. Preserve
            // Cargo's CLI precedence when binding the actual phase-A
            // executables instead of authenticating the metadata default.
            let execution_target_directory =
                cargo_target_dir(args, Some(&selection.target_directory));
            if let Some(execution) = report.test_execution.as_mut() {
                execution.target_directory = Some(execution_target_directory.display().to_string());
            }
            let mut phase_b_started = false;
            let mut granted_plan: Option<trust_test_execution::PreparedTests> = None;
            // A daemon that cannot be established for this phase is the same
            // COULD NOT RUN (3) as at phase A, never flattened into a setup
            // error (2); every other refusal here is a setup error.
            let phase_b = QualifiedTestExecution::dispatch(
                qualified_test_execution.as_ref(),
                &verification_session.id,
                |qualification| -> Result<ExitStatus, ChildSetupError> {
                    if let Some(blocker) = certified_test_execution_platform_blocker() {
                        return Err(blocker.to_string().into());
                    }
                    let execution_authority = write_test_execution_authority(
                        qualification,
                        &verification_session,
                        &execution_target_directory,
                        rustc_path.parent().and_then(Path::parent).ok_or_else(|| {
                            format!(
                                "authenticated compiler path `{}` has no toolchain root",
                                rustc_path.display()
                            )
                        })?,
                        &test_executables,
                        Some(prepared_tests.as_ref().ok_or_else(|| {
                            "native Targo omitted its prepared test plan".to_string()
                        })?),
                    )
                    .map_err(|error| {
                        format!("could not bind Cargo test executables before execution: {error}")
                    })?;
                    if let Some(execution) = report.test_execution.as_mut() {
                        execution.authorized_executables = execution_authority.executables.clone();
                        execution.authorized_inventory_sha256 =
                            Some(execution_authority.inventory_sha256.clone());
                        execution.target_directory =
                            Some(execution_authority.target_directory.clone());
                    }
                    let outcome = process.grant_and_wait(
                        qualification,
                        &verification_session.id,
                        &execution_authority,
                    );
                    phase_b_started = process.execution_started();
                    if phase_b_started {
                        granted_plan = execution_authority.plan.clone();
                    }
                    if phase_b_started {
                        if let Some(execution) = report.test_execution.as_mut() {
                            execution.phase_b_state = CertifiedTestExecutionPhaseState::Started;
                        }
                    }
                    outcome
                },
            );
            executed_test_plan = granted_plan;
            match phase_b {
                Ok(observed_status) => {
                    execution_status = Some(observed_status);
                    let observed = execution_status.as_ref().unwrap();
                    let phase_b_exit = child_status_code(observed);
                    if let Some(execution) = report.test_execution.as_mut() {
                        execution.phase_b_state =
                            CertifiedTestExecutionPhaseState::CargoInvocationExited;
                        execution.phase_b_exit = Some(phase_b_exit);
                    }
                    report.compiler_diagnostics.push(CompilerDiagnostic {
                        level: if observed.success() { "note" } else { "error" }.to_string(),
                        message: format!(
                            "targo trust: certified test execution state=phase-b-cargo-invocation-exited authorized_executables={} cargo_exit_code={phase_b_exit}",
                            test_executables.len(),
                        ),
                    });
                }
                Err(error) => {
                    match &error {
                        ChildSetupError::Setup(error) => eprintln!("targo trust: {error}"),
                        ChildSetupError::CouldNotRun(error) => {
                            eprintln!("targo trust: COULD NOT RUN: {error}")
                        }
                    }
                    report.compiler_diagnostics.push(CompilerDiagnostic {
                        level: "error".to_string(),
                        message: format!(
                            "targo trust: certified test execution state={} error={error}",
                            if phase_b_started {
                                "phase-b-started"
                            } else {
                                "blocked-before-execution"
                            },
                        ),
                    });
                    record_certified_test_execution_error(
                        report.test_execution.as_mut(),
                        phase_b_started,
                        &error.to_string(),
                    );
                    post_phase_a_orchestration_error = Some(error);
                }
            }
        }
    }
    if cargo_test_mode && !cargo_test_compile_only {
        compiler_exit = match &post_phase_a_orchestration_error {
            Some(error) => i32::from(error.exit_code()),
            None => execution_status
                .as_ref()
                .map(child_status_code)
                .unwrap_or_else(|| compile_completion.code()),
        };
        compiler_signal_exit = post_phase_a_orchestration_error
            .is_none()
            .then(|| {
                execution_status
                    .as_ref()
                    .and_then(child_signal_exit_code)
                    .or_else(|| compile_completion.signal_exit())
            })
            .flatten();
        report.duration_ms = start.elapsed().as_millis() as u64;
        if qualified_test_execution.is_some() {
            report.exit_code = compiler_exit;
            report.success &= execution_status.as_ref().is_some_and(ExitStatus::success)
                && post_phase_a_orchestration_error.is_none();
            process_exit = finalize_run_gate(
                &mut report,
                &gate_inputs,
                compiler_exit,
                compiler_signal_exit,
                post_phase_a_orchestration_error.as_ref(),
            );
        } else if let Some(gate) = report.gate.as_mut() {
            gate.test_execution = report.test_execution.clone();
        }
        observe_compiler_errors(
            &mut diagnostic_observer,
            &report.compiler_diagnostics[preexecution_diagnostics..],
        );
        // Tests change run-level state, never the proof-row authority. Rebind
        // the actual execution result before any canonical output is published.
        if let Err(refusal) = report.seal_publication_state() {
            if !test_qualification::publish_seal_refusal(&mut report, &refusal) {
                return ExitCode::from(2);
            }
            process_exit = ExitCode::from(2);
        }
    }

    // T9 and T7c: the compact per-obligation record and the per-package record
    // of the FINAL rows — after the publication seal, whose refusal regrades
    // every row unproved — so the records, the `Summary:` line and the gate
    // read one set of rows. Every crate-mode `check` writes them under the
    // target directory; a live report consumer (`--save-baseline`,
    // `diff --baseline`) reads the same records.
    let obligation_records = {
        let determinism = report.determinism();
        let degraded_anchors: usize = coverage_rows.iter().map(|row| row.degraded_anchors).sum();
        if degraded_anchors > 0 {
            eprintln!(
                "targo trust: {degraded_anchors} obligation key(s) were minted on a degraded \
                 anchor (a span that did not lie in its file's text): those keys are coarser \
                 than a content address"
            );
        }
        crate::obligations::ObligationRecords::of_rows(
            &report.results,
            &function_inventory,
            crate::obligations::RunFacts {
                lane: gate_lane_name(lane).to_string(),
                policy: TrustPolicySelection::from_lane_flags(
                    memory_safe_policy,
                    survey,
                    certify_gate,
                )
                .option_value()
                .unwrap_or("strict")
                .to_string(),
                selection: crate::obligations::canonical_selection(args),
                targo_trust_commit: crate::obligations::targo_trust_commit(),
                profile: budget_profile.id(),
                worker_threads: budget_profile.worker_threads,
                outcome: determinism.outcome,
                vector: determinism.vector.digest(),
                // A unit that concluded without its coverage row leaves the
                // run's coverage unestablished, whatever the other rows sum to.
                coverage_complete: missing_target_coverage.is_empty()
                    && report.coverage.as_ref().is_some_and(|coverage| coverage.coverage_complete),
                degraded_anchors,
            },
            crate::obligations::RunScope {
                selected: cargo_selection
                    .iter()
                    .flat_map(|selection| &selection.packages)
                    .map(|package| package.name.clone())
                    .collect(),
                resolved: cargo_selection
                    .iter()
                    .flat_map(|selection| &selection.resolved_packages)
                    .cloned()
                    .collect(),
            },
            &crate::package_record::RunCoverage {
                rows: &coverage_rows,
                publication_stops: report
                    .publication_boundary
                    .as_ref()
                    .map(|boundary| boundary.elided_stops.as_slice())
                    .unwrap_or_default(),
                missing: missing_target_coverage
                    .iter()
                    .map(|target| target.package_name.clone())
                    .collect(),
                compile_errors: &compile_errors,
            },
        )
        // PKG-LIVE-2: the island rows each unit published, by its package,
        // and the package of every proof unit the run declared, so a unit that
        // published none is told apart from one with no island. Disclosure for
        // the records and the changed-only view: the facts, vector, coverage
        // and every count above are computed without them.
        .with_clean_islands(
            cargo_proof_inventory
                .as_ref()
                .map(|inventory| {
                    inventory
                        .proof_targets
                        .iter()
                        .map(|target| target.package_name.as_str())
                        .collect::<Vec<_>>()
                })
                .as_deref(),
            clean_island_rows.iter().map(|(target, rows)| (target.package_name.as_str(), rows)),
        )
    };
    // Live-edit-loop step 2: a test run that executed (or was refused before
    // executing) its harnesses carries each case's outcome as its harness
    // reported it (`crate::test_results`). Disclosure only: the verdict, the
    // gate and the exit status above never read it.
    let obligation_records = if cargo_test_mode && !cargo_test_compile_only {
        let harnesses: Vec<crate::test_results::AuthorizedHarness> = test_executables
            .iter()
            .map(|executable| crate::test_results::AuthorizedHarness {
                package: executable.target.package_name.clone(),
                key: crate::test_results::harness_key(
                    &executable.target.target_kinds,
                    &executable.target.target_name,
                ),
                executable: executable
                    .path
                    .canonicalize()
                    .unwrap_or_else(|_| executable.path.clone())
                    .display()
                    .to_string(),
            })
            .collect();
        let execution = match &executed_test_plan {
            Some(plan) => {
                crate::test_results::Execution::Ran { session: &verification_session.id, plan }
            }
            None if test_execution_refused => crate::test_results::Execution::NotRun(
                "test execution could not be set up after compilation".to_string(),
            ),
            None if qualified_test_execution.is_none() => crate::test_results::Execution::NotRun(
                "the frontend proof gate did not pass".to_string(),
            ),
            None => crate::test_results::Execution::NotRun(
                "execution was refused before any harness started".to_string(),
            ),
        };
        // What chose the cases: the executed plan's harness arguments, or,
        // when no harness ran, the arguments the caller gave after `--`.
        let arguments = match &executed_test_plan {
            Some(plan) => crate::test_results::harness_arguments(plan),
            None => args.iter().skip_while(|arg| *arg != "--").skip(1).cloned().collect(),
        };
        obligation_records
            .with_tests(crate::test_results::collect(&harnesses, execution), arguments)
    } else {
        obligation_records
    };
    let mut delta_view: Option<crate::agent_delta::DeltaView> = None;
    let check_run = args.first().is_some_and(|arg| arg == "check");
    if crate_mode && (check_run || obligation_records.tests.is_some()) {
        let target_dir = cargo_target_dir(
            args,
            cargo_selection.as_ref().map(|selection| selection.target_directory.as_path()),
        );
        // Observational artifacts: a write failure is reported, never a
        // verdict and never an exit status. A test run writes none: the files
        // under `trust/obligations` are a check's, and a test run's record
        // lives in its snapshot (`crate::agent_delta`).
        if check_run {
            if let Err(error) = obligation_records.write_records(&target_dir) {
                eprintln!(
                    "targo trust: warning: could not write the obligation and package records \
                     under `{}`: {error}",
                    target_dir.join("trust").display()
                );
            }
        }
        // Live-edit-loop step 2: snapshot each selected package's record (the
        // same bytes just written) and compare it with the caller's base; the
        // caller's pointer moves only once the report printed the view
        // (`render_report_for_run`). Observational, like the records: no
        // verdict or exit reads it.
        if let Some(request) = agent_delta {
            delta_view = Some(crate::agent_delta::publish_run(
                &target_dir,
                &obligation_records,
                request,
                crate::agent_delta::caller_session_from_env().as_deref(),
            ));
        }
    }

    if evidence_setup_failed && live_report_consumer.is_some() {
        report_setup_failure(
            &mut diagnostic_observer,
            format_args!(
                "targo trust: live report consumer withheld: compiler/Cargo evidence setup failed"
            ),
        );
    } else if let Some(consumer) = live_report_consumer.as_mut() {
        if let Some(reason) = live_report_consumer_rejection(LiveReportConsumerInput {
            crate_mode,
            compiler_exit,
            compiler_signal_exit,
            cargo_proof_inventory: report.cargo_proof_inventory.as_ref(),
            coverage: coverage.as_ref(),
            missing_target_coverage: &missing_target_coverage,
            raw_terminal_inventory_complete,
            compiled_targets: &compiled_targets,
            observed_proof_targets: &observed_proof_targets,
            completed_proof_targets: &completed_proof_targets,
            coverage_proof_targets: &coverage_proof_targets,
        }) {
            report_setup_failure(
                &mut diagnostic_observer,
                format_args!("targo trust: live report consumer withheld: {reason}"),
            );
        } else {
            let live_report = match report.sealed_canonical_report() {
                Ok(report) => report.with_obligations(obligation_records),
                Err(error) => {
                    report_setup_failure(
                        &mut diagnostic_observer,
                        format_args!("targo trust: live report authority gate failed: {error}"),
                    );
                    return ExitCode::from(2);
                }
            };
            if let Err(error) = consumer(&live_report) {
                eprintln!("targo trust: live report consumer failed: {error}");
                return ExitCode::from(2);
            }
        }
    }

    if render_output == ReportRendering::Suppressed
        && (report_dir.is_some() || unsafe_memory_report.is_some())
    {
        report_artifact_failure(
            &mut diagnostic_observer,
            format_args!(
                "targo trust: internal error: suppressed rendering cannot satisfy requested report artifacts"
            ),
        );
        return ExitCode::from(2);
    }

    let native_expected = cargo_proof_inventory
        .as_ref()
        .map(|inventory| inventory.proof_targets.clone())
        .unwrap_or_default();
    let native_admission = crate::compiler_admission::Report::new(
        &native_expected,
        &compiled_targets,
        native_admission_observations,
        native_admission_problems,
    );
    let evidence_bundle = match render_report_for_run(
        &report,
        render_output,
        format,
        report_dir,
        unsafe_memory_report,
        evidence_bundle_required(lane, unsafe_memory_report.is_some()),
        crate::report::CompilerResourceReports {
            memory: Some(&compiler_memory_observations),
            admission: Some(&native_admission),
        },
        delta_view.as_ref(),
        &mut diagnostic_observer,
    ) {
        Ok(status) => status,
        Err(_) => return ExitCode::from(2),
    };

    // Trust (dep-TCB ledger, Stage 0): surface every dependency scoped out of
    // verification plus the unconditional foundational core/alloc/std residual
    // TCB. A local stdlib subject can emit selected behavioral obligations
    // without closing that residual surface. Only in crate mode (single-file
    // builds have no resolved dep graph), and never gated on success: the trust
    // base is reported whether or not the obligations passed.
    if crate_mode && render_output == ReportRendering::Stdout {
        let ledger = crate::dep_tcb::dep_tcb_ledger_lines(cargo_proof_inventory.as_ref());
        if !ledger.is_empty() {
            let mut rendered = String::new();
            trust_report::append_dep_tcb_ledger(&mut rendered, &ledger);
            eprintln!("{rendered}");
        }
        // Repeat the Kani-surface disclosure next to the verdict it qualifies,
        // so it is not lost in the scrollback above the report.
        if let Some(disclosure) = super::kani_gate::inherited_kani_surface_disclosure(cmd_args) {
            eprintln!("targo trust: {disclosure}");
        }
    }

    // Trust (blocker 4, 2026-10-01): the verdict, Gate line and ledger above
    // are published even when the report bundle had to omit evidence. Whether
    // that costs the exit code depends on whether this run ASKED for evidence.
    // A missing-trust-json diagnostic is printed either way: the bundle
    // override must not hide the more fundamental failure.
    let (closing_lines, closing_exit) = closing_exit_disclosures(
        lane,
        unsafe_memory_report.is_some(),
        evidence_bundle.as_ref(),
        missing_trust_json.as_deref(),
        process_exit,
    );
    for line in &closing_lines {
        eprintln!("{line}");
    }
    if let Some(exit) = closing_exit {
        return exit;
    }
    if !cargo_evidence_integrity_errors.is_empty() {
        return process_exit;
    }

    if process_exit == ExitCode::SUCCESS {
        verification_session.publish_proof_hints();
    }
    process_exit
}

/// The existing sealed renderer, with an explicit artifact-only destination.
/// An output failure can invalidate an audit measurement after its live callback.
pub(crate) fn render_report_for_run(
    report: &VerificationReport,
    rendering: ReportRendering,
    format: OutputFormat,
    report_dir: Option<&str>,
    unsafe_memory_report: Option<&UnsafeMemoryReportRequest>,
    evidence_required: bool,
    resources: crate::report::CompilerResourceReports<'_>,
    delta: Option<&crate::agent_delta::DeltaView>,
    observer: &mut Option<CompilerDiagnosticObserver<'_>>,
) -> std::io::Result<Option<crate::report::EvidenceBundleStatus>> {
    if rendering == ReportRendering::Suppressed {
        return Ok(None);
    }
    let mut stdout = std::io::stdout();
    let mut sink = std::io::sink();
    let (format, output): (_, &mut dyn std::io::Write) =
        if rendering == ReportRendering::ArtifactsOnly {
            (OutputFormat::Json, &mut sink)
        } else {
            (format, &mut stdout)
        };
    let result = report.render_published_with_compiler_resources(
        format,
        report_dir,
        unsafe_memory_report,
        evidence_required,
        resources,
        delta,
        output,
    );
    match &result {
        Err(error) => report_artifact_failure(
            observer,
            format_args!("targo trust: report artifact evidence gate failed: {error}"),
        ),
        Ok(status)
            if rendering == ReportRendering::ArtifactsOnly
                && report_dir.is_some()
                && status.as_ref().is_none_or(|bundle| !bundle.complete) =>
        {
            report_artifact_failure(
                observer,
                format_args!("targo trust: requested audit report bundle is incomplete"),
            );
        }
        _ => {}
    }
    // The renderer returns `Ok` only after it printed the view (in every
    // format), so only now does the caller's pointer move to the token it
    // names (`crate::agent_delta`): a run whose report fails to render leaves
    // the caller's base where it was.
    if let (Ok(_), Some(view)) = (&result, delta) {
        for note in view.commit_pointers() {
            eprintln!("note: {note}");
        }
    }
    result
}

/// Whether this run ASKED for a complete saved evidence bundle: every lane but
/// the explicit advisory ramp, and any `--unsafe-memory` request.
fn evidence_bundle_required(lane: GateLane, unsafe_memory_requested: bool) -> bool {
    unsafe_memory_requested || lane != GateLane::Advisory
}

/// The stderr lines that close a rendered run, and the exit they force (`None`:
/// fall through to the remaining exit logic with `process_exit`).
///
/// A missing-trust-json diagnostic comes FIRST and is never suppressed by the
/// incomplete-bundle override (both fail the run; the diagnostic names the
/// more fundamental failure).
fn closing_exit_disclosures(
    lane: GateLane,
    unsafe_memory_requested: bool,
    evidence_bundle: Option<&crate::report::EvidenceBundleStatus>,
    missing_trust_json: Option<&str>,
    process_exit: ExitCode,
) -> (Vec<String>, Option<ExitCode>) {
    let mut lines = Vec::new();
    if let Some(diagnostic) = missing_trust_json {
        lines.push(format!("targo trust: error: {diagnostic}"));
    }
    if let Some(code) =
        evidence_bundle_exit_override(lane, unsafe_memory_requested, evidence_bundle)
    {
        let demand = if unsafe_memory_requested {
            "`--unsafe-memory` wrapper".to_string()
        } else {
            format!("{} lane", gate_lane_name(lane))
        };
        lines.push(format!(
            "targo trust: report artifact evidence gate failed: the saved evidence bundle is incomplete and the {demand} requires a complete one; exiting {code} (the `Sealed gate` line above records the sealed verdict's own exit, which this overrides)"
        ));
        return (lines, Some(ExitCode::from(code)));
    }
    if missing_trust_json.is_some() {
        return (lines, Some(process_exit));
    }
    (lines, None)
}

fn gate_lane_name(lane: GateLane) -> &'static str {
    match lane {
        GateLane::Advisory => "advisory",
        GateLane::Strict => "strict",
        GateLane::Certify => "certify",
        GateLane::MemorySafe => "memory-safe",
    }
}

/// Exit code an INCOMPLETE saved evidence bundle forces, if any.
///
/// Only the explicitly advisory lane (`--allow-l0-gaps`, the ramp) exits per
/// its verdict over an incomplete bundle — its stderr says so next to the
/// `Gate:` line. Every other lane (strict, the default; `--certify`; the
/// narrow memory-safe lane) and any `--unsafe-memory` request asked for
/// EVIDENCE, so a bundle that cannot be re-checked keeps the run failing.
///
/// The code is 2, not a new one: 2 is what these runs exited with before the
/// fix, for this very condition ("report artifact evidence gate failed"), so
/// no caller's contract changes — the run only stops discarding the verdict.
/// A distinct code would amend the CLI contract and needs its own recorded decision.
fn evidence_bundle_exit_override(
    lane: GateLane,
    unsafe_memory_requested: bool,
    evidence_bundle: Option<&crate::report::EvidenceBundleStatus>,
) -> Option<u8> {
    const INCOMPLETE_EVIDENCE_BUNDLE_EXIT: u8 = 2;
    let incomplete = evidence_bundle.is_some_and(|status| !status.complete);
    (incomplete && evidence_bundle_required(lane, unsafe_memory_requested))
        .then_some(INCOMPLETE_EVIDENCE_BUNDLE_EXIT)
}

/// `targo trust test` ran the tests (its execution phase reached Cargo's
/// exit) and they failed.
fn tests_failed(execution: Option<&CertifiedTestExecutionReport>) -> bool {
    execution.and_then(|execution| execution.phase_b_exit).is_some_and(|exit| exit != 0)
}

/// What decides a verified run's exit once the setup, evidence and signal
/// exits are ruled out ([`RunExit::decide`]).
#[derive(Clone, Copy, Debug)]
struct RunExitFacts {
    /// The lane passed (and no hardened, evidence or exclusion gate failed).
    report_success: bool,
    /// The compiler's own exit status; in `targo trust test`, once the tests
    /// ran, their Cargo invocation's.
    compiler_exit: i32,
    /// The authenticated coverage inventory is present, complete and covers
    /// every completed target: the verification session concluded.
    verification_concluded: bool,
    /// The session concluded and the gate counts hold a non-proved row.
    fail_closed_rows_observed: bool,
    /// The session concluded and every proof unit the run declared reached its
    /// terminal summary: none stopped short of verification (a compile error,
    /// a dependency that failed, a unit Cargo never started).
    every_unit_concluded: bool,
    /// The published rows alone fail the lane: its gate over them, with a
    /// clean compiler exit, is no pass. Only such rows are trustc's
    /// fail-closed errors, so only they can account for a nonzero exit.
    rows_fail_the_lane: bool,
    /// `targo trust test` ran the tests and they failed: `compiler_exit` is
    /// their Cargo invocation's status, which no row accounts for.
    tests_failed: bool,
    /// A gate a re-run cannot change failed: the hardened proof-evidence gate,
    /// or an active Cargo Unit excluded outside the dependency-TCB ledger.
    configuration_gate_failed: bool,
    /// At least one published row is failed.
    refuted: bool,
    /// The determinism outcome of the published rows and the backstop ledger
    /// (plan §2).
    outcome: trust_types::determinism::UnitOutcome,
}

impl RunExitFacts {
    /// The run failed for its verification alone: the compiler exited 0, or
    /// every declared unit concluded and rows that fail the lane account for
    /// the nonzero exit. A failure they cannot account for (a compile error in
    /// a unit that never concluded, a link error in a run whose rows pass the
    /// lane) is no question of measurement, and re-running cannot change it.
    /// Rows that fail the lane AND a compile error in a unit whose
    /// verification had concluded cannot be told apart here: both are that
    /// unit's errors.
    fn failure_is_verifications(&self) -> bool {
        self.compiler_exit == 0
            || (self.every_unit_concluded
                && self.fail_closed_rows_observed
                && self.rows_fail_the_lane)
    }
}

/// How a verified run's exit status was decided (the CLI contract,
/// `targo trust --help` "Exit codes").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RunExit {
    /// The lane passed and the rows are a measurement: 0.
    Passed,
    /// A verdict: a refuted obligation, or an unproved one the lane does not
    /// admit: 1.
    Verdict,
    /// The rows are no measurement, none was refuted, and they alone failed
    /// the run: 3 ([`crate::determinism_report::EXIT_COULD_NOT_RUN`]).
    CouldNotRun,
    /// The compiler, or the tests, ended for reasons other than verification:
    /// their own status.
    Compiler(u8),
}

impl RunExit {
    /// Decide, in this order:
    /// 1. a pass that is a measurement exits 0;
    /// 2. a session that did not conclude keeps the compiler's own nonzero
    ///    status (an ICE after a proved prefix, a compile error): it says more
    ///    than any count of the rows before it
    ///    (`live_report_consumer_cannot_override_early_proof_followed_by_ice`);
    /// 3. a refuted row is a verdict (1) even when the rows are no
    ///    measurement: a counterexample is a solved stop, and reporting it as
    ///    COULD NOT RUN would let a consumer read a real defect as a run to
    ///    retry. `diff --baseline` ranks a LOST proof or a new refutation
    ///    above NOT MEASURED the same way;
    /// 4. tests that ran and failed keep their own status: no row accounts
    ///    for a failing test, however its rows were decided;
    /// 5. rows that are no measurement — outcome `could-not-run` or
    ///    `not-reproducible` — exit 3 when they alone failed the run
    ///    ([`RunExitFacts::failure_is_verifications`]) and no gate a re-run
    ///    cannot change failed: an unknown there may be a clock's, so neither
    ///    a pass nor an unproved verdict can be read from them (plan §2,
    ///    §3.1, §4.8). A failure they do not account for maps as in 6;
    /// 6. otherwise exit 1 for a concluded session with a non-proved row, the
    ///    compiler's own nonzero status, or 1.
    fn decide(facts: RunExitFacts) -> Self {
        use trust_types::determinism::UnitOutcome;
        let measured = facts.outcome == UnitOutcome::Measured;
        let compiler_code = u8::try_from(facts.compiler_exit).ok().filter(|code| *code != 0);
        if facts.report_success && measured {
            return RunExit::Passed;
        }
        if !facts.verification_concluded {
            if let Some(code) = compiler_code {
                return RunExit::Compiler(code);
            }
        }
        if facts.refuted {
            return RunExit::Verdict;
        }
        if facts.tests_failed {
            if let Some(code) = compiler_code {
                return RunExit::Compiler(code);
            }
        }
        if !measured && !facts.configuration_gate_failed && facts.failure_is_verifications() {
            return RunExit::CouldNotRun;
        }
        if facts.fail_closed_rows_observed {
            return RunExit::Verdict;
        }
        compiler_code.map_or(RunExit::Verdict, RunExit::Compiler)
    }

    fn code(self) -> u8 {
        match self {
            RunExit::Passed => 0,
            RunExit::Verdict => 1,
            RunExit::CouldNotRun => crate::determinism_report::EXIT_COULD_NOT_RUN,
            RunExit::Compiler(code) => code,
        }
    }
}

/// Trust (green front door, Stage 2): build the serializable gate object from
/// the gate decision, the outcome partition, and the crate-scope ledger. The
/// `exit_code` is the already-finalized REAL process exit, so it can never claim
/// 0 or an ordinary gate failure while another gate (hardened evidence,
/// missing-json, or compiler setup) chooses a different status. `decision`
/// has already incorporated exact active-Unit exclusions from the canonical
/// Cargo proof inventory. Ledger entries only populate
/// `conditional_on_dependency_entries`; curated sysroot assumptions do not
/// independently drive the decision or terminal label.
fn build_verification_gate_report(
    lane: GateLane,
    verification_level: &str,
    decision: GateDecision,
    counts: OutcomeCounts,
    process_exit_code: u8,
    dep_assumptions: &[trust_types::AssumptionEntry],
    coverage: Option<trust_types::VerificationCoverage>,
) -> trust_types::VerificationGateReport {
    trust_types::VerificationGateReport {
        lane: lane.as_str().to_string(),
        verification_level: Some(verification_level.to_string()),
        decision: decision.as_str().to_string(),
        exit_code: process_exit_code,
        counts: trust_types::VerificationGateCounts {
            total: counts.total,
            proved: counts.proved,
            failed: counts.failed,
            unknown: counts.unknown,
            runtime_checked: counts.runtime_checked,
            assumed: counts.assumed,
            mandated: counts.mandated,
            contract_panics: counts.contract_panics,
            excluded: counts.excluded,
        },
        conditional_on_assumption_rows: counts.assumed > 0,
        conditional_on_dependency_entries: !dep_assumptions.is_empty(),
        conditional_on_runtime_checks: counts.runtime_checked > 0,
        // Ramp: set only when the advisory lane passed conditionally on genuine
        // unknowns. Every other lane keeps an unknown fatal, so this is false
        // there and can never claim a condition of a pass that did not happen.
        conditional_on_unknown_rows: matches!(
            decision,
            GateDecision::ConditionalPass { unknown, .. } if unknown > 0
        ),
        conditional_on_visitation_entries: false,
        // Trust (assertion-grade coverage): the counts + `coverage_complete`
        // recorded into report.json; `None` = coverage unknown (older compiler).
        coverage,
        test_execution: None,
        exclusions: Vec::new(),
        // Both filled once the published rows are final (`VerificationReport::
        // record_determinism`), which is after this gate is built.
        determinism: None,
        failure_sites: None,
        project_requirements: None,
    }
}

// ---------------------------------------------------------------------------
// Compiler capture (for rewrite loop)
// ---------------------------------------------------------------------------

/// Outcome of a single compiler invocation, for use in the rewrite loop.
pub(crate) struct CompilerRunResult {
    pub(crate) exit_code: i32,
    pub(crate) signal_exit: Option<u8>,
    pub(crate) report_subject: String,
    pub(crate) verification_results: Vec<VerificationResult>,
    pub(crate) zero_obligation_functions: Vec<String>,
    /// Trust (CB4): the authenticated libtest harness exclusion inventory.
    pub(crate) test_harness_exclusions: Vec<trust_types::GateExclusionReport>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) coverage: Option<trust_types::VerificationCoverage>,
    pub(crate) missing_target_coverage: Vec<CargoTargetIdentity>,
    pub(crate) live_transport_authority: LiveTransportAuthority,
    /// Whether the published rows and the backstop ledger are a measurement
    /// (plan §2), as a report of the same run would record it.
    pub(crate) outcome: trust_types::determinism::UnitOutcome,
}

pub(super) struct CompilerCaptureInput<'a> {
    pub(super) cmd_args: &'a [String],
    pub(super) rustc_path: &'a Path,
    pub(super) config: &'a TrustConfig,
    pub(super) selected_codegen_backend: Option<&'a str>,
    pub(super) supports_json_transport: bool,
    pub(super) strict_artifact_policy: bool,
    pub(super) allow_l0_gaps: bool,
    pub(super) memory_safe_policy: bool,
    pub(super) survey: bool,
    pub(super) certify_gate: bool,
    pub(super) hardened: bool,
    pub(super) trust_profile: Option<&'a str>,
    pub(super) quiet: bool,
    pub(super) ephemeral_single_file_output: bool,
}

/// Run a compiler command and capture verification results without rendering.
///
/// Unlike `run_compiler`, this returns the results for loop processing rather
/// than rendering a report and exiting.
pub(super) fn run_compiler_capture(
    input: CompilerCaptureInput<'_>,
) -> Result<CompilerRunResult, ExitCode> {
    let CompilerCaptureInput {
        cmd_args,
        rustc_path,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        memory_safe_policy,
        survey,
        certify_gate,
        hardened,
        trust_profile,
        quiet,
        ephemeral_single_file_output,
    } = input;
    if cmd_args.is_empty() {
        eprintln!("targo trust: internal error: empty command");
        return Err(ExitCode::from(2));
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    let crate_mode = is_cargo_program(program);
    let cargo_execution_mode =
        crate_mode && args.first().is_some_and(|arg| matches!(arg.as_str(), "test" | "bench"));
    // This capture path feeds the source-rewrite loop and has no
    // evidence-gated second execution phase. Keep this defense in depth even
    // though the CLI rejects `test --rewrite`: an internal caller must not
    // revive compile-and-execute-before-admission behavior.
    if cargo_execution_mode {
        eprintln!(
            "targo trust: test/bench execution is unavailable in rewrite capture mode; run without `--rewrite`"
        );
        return Err(ExitCode::from(2));
    }
    if crate_mode {
        if let Some(error) = cargo_compiler_override_diagnostic(args) {
            eprintln!("targo trust: {error}");
            return Err(ExitCode::from(2));
        }
        if !supports_json_transport {
            eprintln!(
                "targo trust: selected compiler lacks the structured Trust transport required for evidence-grade Cargo verification"
            );
            return Err(ExitCode::from(2));
        }
    }
    let verification_session = match VerificationSession::create() {
        Ok(session) => session.with_proof_store(),
        Err(error) => {
            eprintln!("targo trust: could not create verification freshness token: {error}");
            return Err(ExitCode::from(2));
        }
    };
    let hardened_profile = hardened_profile_name(hardened, trust_profile).map(str::to_string);
    // Same requirement merge as run_compiler, refused before any compiler runs.
    let requirements = requirement_flags_for_run(
        config,
        memory_safe_policy,
        survey,
        certify_gate,
        allow_l0_gaps,
        hardened_profile.as_deref(),
    )
    .map_err(|error| {
        eprintln!("targo trust: {error}");
        ExitCode::from(2)
    })?;
    let budget_profile = crate::determinism_report::budget_profile(config);
    let controls = VerificationControls {
        policy: TrustPolicySelection::from_lane_flags(memory_safe_policy, survey, certify_gate),
        budget: &budget_profile,
        hardened_profile: hardened_profile.as_deref(),
        verification_session: &verification_session.id,
        proof_artifact_root: verification_session.artifact_root(),
        // The rewrite-capture lane never publishes spec goals: its compiles
        // are exploratory, and a spec artifact must come from the canonical
        // verification run the user asked about.
        spec_emit_dir: None,
    };
    let mut effective_args = if crate_mode {
        cargo_args_with_proof_message_format(args).map_err(|error| {
            eprintln!("targo trust: could not establish Cargo proof message format: {error}");
            ExitCode::from(2)
        })?
    } else {
        args.to_vec()
    };
    if !crate_mode {
        if let Err(error) = append_verification_control_args(&mut effective_args, &controls) {
            eprintln!("targo trust: could not configure verifier options: {error}");
            return Err(ExitCode::from(2));
        }
        requirements.apply_to_args(&mut effective_args);
    }
    let _ephemeral_output =
        match prepare_ephemeral_single_file_output(args, ephemeral_single_file_output) {
            Ok(output) => output,
            Err(error) => {
                eprintln!("targo trust: could not prepare temporary single-file output: {error}");
                return Err(ExitCode::from(2));
            }
        };
    let mut cmd = Command::new(program);
    cmd.args(&effective_args);
    scrub_proof_compiler_authority_env(&mut cmd);
    cmd.stderr(Stdio::piped());
    if crate_mode {
        cmd.stdout(Stdio::piped());
    }
    apply_native_runtime_env(&mut cmd, rustc_path);

    let cargo_selection = if crate_mode {
        match resolve_cargo_selection_for_compiler(args, rustc_path, program) {
            Ok(selection) => Some(selection),
            Err(error) => {
                eprintln!(
                    "targo trust: could not resolve canonical Cargo package selection: {error}"
                );
                return Err(ExitCode::from(2));
            }
        }
    } else {
        None
    };
    let selected_cargo_packages = cargo_selection.as_ref().map(selected_package_map_from_selection);
    if crate_mode {
        cmd.env("TRUST_TARGO_VERIFY", "1");
        apply_cargo_child_rustc_env(&mut cmd, rustc_path);
        if let Err(error) = apply_lane_flags_env(LaneFlagsInput {
            cmd: &mut cmd,
            config,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
            controls: &controls,
            requirements: &requirements,
            cargo_args: cmd_args,
        }) {
            eprintln!("targo trust: could not configure Cargo verifier options: {error}");
            return Err(ExitCode::from(2));
        }
        if let Err(error) = apply_crate_memory_coordination(
            &mut cmd,
            args,
            cargo_selection.as_ref().map(|selection| selection.target_directory.as_path()),
        ) {
            return Err(error.report("could not establish memory coordination"));
        }
    }

    CompilerProcessGuard::configure(&mut cmd);
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("targo trust: failed to spawn `{program}`: {e}");
            return Err(ExitCode::from(2));
        }
    };
    let mut process_guard = CompilerProcessGuard::start(
        child.id(),
        CompilerProcessBounds::from_backstop(config.backstop),
    );

    let cargo_stdout = if crate_mode {
        let Some(stdout) = child.stdout.take() else {
            process_guard.abort_before_reap(&mut child);
            let _ = child.wait();
            return Err(ExitCode::from(2));
        };
        let selected = selected_cargo_packages
            .as_ref()
            .expect("crate mode has canonical package selection")
            .clone();
        Some(spawn_cargo_stdout_parser(
            stdout,
            process_guard.progress(),
            selected,
            verification_session.id.clone(),
            strict_artifact_policy,
            cargo_execution_mode,
            false,
        ))
    } else {
        None
    };

    let Some(stderr) = child.stderr.take() else {
        eprintln!("targo trust: compiler stderr pipe was not available");
        process_guard.abort_before_reap(&mut child);
        let _ = child.wait();
        return Err(ExitCode::from(2));
    };
    let stderr_output = spawn_compiler_stderr_parser(
        stderr,
        process_guard.progress(),
        crate_mode,
        !quiet,
        supports_json_transport,
        verification_session.id.clone(),
        strict_artifact_policy,
    );

    let status = match wait_for_compiler_process(&mut child, &mut process_guard) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("targo trust: failed to wait for process: {e}");
            return Err(ExitCode::from(2));
        }
    };
    if let Err(error) = process_guard.finish() {
        return Err(backstop_ended_the_compiler(&error, config.backstop));
    }

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics;
    let mut coverage_rows = Vec::new();
    let mut coverage_proof_targets = BTreeSet::new();
    let mut observed_proof_targets = BTreeSet::new();
    let mut completed_proof_targets = BTreeSet::new();
    let mut compiled_targets = BTreeSet::new();

    let parsed_stderr = match receive_compiler_output(stderr_output, "compiler stderr") {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust: invalid compiler stderr channel: {error}");
            return Err(ExitCode::from(2));
        }
    };
    if crate_mode {
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
    } else {
        verification_results = parsed_stderr.verification_results;
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
        coverage_rows = parsed_stderr.coverage_rows;
    }
    if let Some(channel) = cargo_stdout {
        let evidence = match receive_compiler_output(channel, "canonical Cargo stdout") {
            Ok(evidence) => evidence,
            Err(error) => {
                eprintln!("targo trust: invalid canonical Cargo evidence channel: {error}");
                return Err(ExitCode::from(2));
            }
        };
        if status.success() {
            let selected = selected_cargo_packages
                .as_ref()
                .expect("crate mode has canonical package selection");
            if let Err(error) =
                evidence.require_successful_selected_roots(selected, strict_artifact_policy)
            {
                eprintln!("targo trust: invalid successful Cargo proof inventory: {error}");
                return Err(ExitCode::from(2));
            }
        }
        let parsed = evidence.parsed.require_structured_json_transport(true);
        verification_results = parsed.verification_results;
        compiler_diagnostics.extend(parsed.compiler_diagnostics);
        coverage_rows = parsed.coverage_rows;
        coverage_proof_targets = parsed.coverage_proof_targets;
        observed_proof_targets = parsed.observed_proof_targets;
        completed_proof_targets = parsed.completed_proof_targets;
        compiled_targets = evidence.compiled_targets;
    }

    let coverage = aggregate_coverage(&coverage_rows);
    let noted_stops = crate::determinism_report::merged_noted_stops(&coverage_rows);
    let missing_target_coverage =
        completed_proof_targets.difference(&coverage_proof_targets).cloned().collect();
    let report_subject = if crate_mode {
        cargo_report_subject(&compiled_targets, &observed_proof_targets, &completed_proof_targets)
    } else {
        match single_file_report_subject(cmd_args) {
            Ok(subject) => subject,
            Err(error) => {
                eprintln!("targo trust: {error}");
                return Err(ExitCode::from(2));
            }
        }
    };

    // Retain the exact authenticated vector before projecting it for rewrite
    // publication.  Inlining first makes the authority self-contained after
    // the private per-run store is deleted; normalization then validates those
    // same bytes without reopening a path-backed artifact.  That only holds
    // when EVERY artifact was inlined: past the inline budget an artifact
    // stays path-backed, and once the private store is deleted it could no
    // longer earn proof credit.  This lane has no surviving store, so it
    // refuses loudly (as main did at the old inline cap) rather than silently
    // downgrading those rows.
    let mut authenticated_compiler_results = verification_results;
    match crate::report::inline_verification_result_artifacts(
        &mut authenticated_compiler_results,
        verification_session.artifact_root(),
    ) {
        Ok(0) => {}
        Ok(still_path_backed) => {
            eprintln!(
                "targo trust: {still_path_backed} captured proof artifact(s) exceed the inline budget and cannot outlive the private run store; refusing rather than silently dropping their proof credit"
            );
            return Err(ExitCode::from(2));
        }
        Err(error) => {
            eprintln!(
                "targo trust: could not retain captured proof artifacts before deleting the private run store: {error}"
            );
            return Err(ExitCode::from(2));
        }
    }
    let zero_obligation_functions =
        crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
    let test_harness_exclusions =
        crate::types::authenticated_test_harness_exclusions(&authenticated_compiler_results);
    let mut verification_results = authenticated_compiler_results.clone();
    let publication_boundary = crate::types::normalize_authenticated_results_for_publication(
        &mut verification_results,
        None,
    );
    let noted_stops = crate::determinism_report::noted_stops_with_publication(
        &noted_stops,
        &publication_boundary.elided_stops,
        None,
    );
    let Some(live_transport_authority) = LiveTransportAuthority::capture_authenticated_projection(
        &report_subject,
        &verification_session.id,
        authenticated_compiler_results,
        &verification_results,
        None,
        // The rewrite-capture lane deliberately keeps STRICT classification:
        // its verdict drives `rewrite_iteration_success`, and the loop must not
        // stop strengthening a crate because a test-target panic was recorded
        // as a condition.
        TestTargetPanicPolicy::Strict,
    ) else {
        eprintln!(
            "targo trust: captured compiler rows did not match their authenticated publication projection; fail-closed"
        );
        return Err(ExitCode::from(2));
    };

    let outcome =
        crate::determinism_report::UnitDeterminism::of_rows(&verification_results, &noted_stops)
            .outcome;
    if status.success() {
        verification_session.publish_proof_hints();
    }
    Ok(CompilerRunResult {
        outcome,
        exit_code: child_status_code(&status),
        signal_exit: child_signal_exit_code(&status),
        report_subject,
        verification_results,
        zero_obligation_functions,
        test_harness_exclusions,
        compiler_diagnostics,
        coverage,
        missing_target_coverage,
        live_transport_authority,
    })
}

// ---------------------------------------------------------------------------
// Rewrite loop
// ---------------------------------------------------------------------------

/// Run the prove-strengthen-backprop convergence loop.
///
/// Uses the ad-hoc CLI rewrite loop implementation.
pub(crate) fn run_rewrite_loop(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> ExitCode {
    run_rewrite_loop_fallback(
        rustc,
        subcommand,
        sub_args,
        config,
        selected_codegen_backend,
        supports_json_transport,
    )
}

/// The prove step of one rewrite-loop iteration: build the command for the
/// source as it stands on disk right now and capture the compiler's verdict on
/// it. That verdict is what grades the previous iteration's edits.
fn rewrite_loop_prove_once(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    quiet: bool,
) -> Result<(Vec<String>, CompilerRunResult), ExitCode> {
    let cmd_args = build_native_command_with_json_transport(
        rustc,
        subcommand,
        sub_args,
        config,
        selected_codegen_backend,
        supports_json_transport,
    )
    .map_err(|error| {
        eprintln!("targo trust: error: {error}");
        ExitCode::from(2)
    })?;
    let run_result = run_compiler_capture(CompilerCaptureInput {
        cmd_args: &cmd_args,
        rustc_path: rustc,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy: sub_args.strict_artifact_policy(),
        allow_l0_gaps: sub_args.allow_l0_gaps_lane(),
        memory_safe_policy: sub_args.memory_safe && !sub_args.survey,
        survey: sub_args.survey,
        certify_gate: sub_args.certify_lane(),
        hardened: sub_args.hardened,
        trust_profile: sub_args.trust_profile.as_deref(),
        quiet,
        ephemeral_single_file_output: sub_args.is_single_file
            && !matches!(subcommand, Subcommand::Build | Subcommand::Test)
            && !has_output_path_flag(&sub_args.passthrough),
    })?;
    if let Some(signal_exit) = run_result.signal_exit {
        // A killed compiler is an execution failure, not a proof frontier
        // that the rewrite loop can strengthen. Preserve its conventional
        // shell status instead of collapsing every signal to exit 1.
        return Err(ExitCode::from(signal_exit));
    }
    Ok((cmd_args, run_result))
}

/// Ad-hoc CLI rewrite loop.
fn run_rewrite_loop_fallback(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> ExitCode {
    use crate::rewrite_loop::{
        BackpropEngine, BackpropResult, ConvergenceTracker, LoopDecision, RepairArtifact,
        RepairIteration, RepairRunSummary, UnverifiedRewrites, append_audit_entries,
        binary_source_backpropagation_blockers, build_rewrite_records, decision_label,
        describe_restore, print_ai_repair_prompts_for_results, print_iteration_header,
        print_iteration_summary, print_loop_summary, rewrite_rejection,
        strengthen_failures_with_binary_source_provenance, write_repair_artifact,
        write_repair_markdown,
    };
    let mut audit_trail = trust_backprop::AuditTrail::new();

    let max_iterations = sub_args.max_iterations;

    // Intent is a first-class repair input: a design doc / chat that guides what
    // the AI repair should aim for. Resolved once for the whole loop.
    let repair_intent = match crate::intent::resolve_intent(
        sub_args.intent.as_deref(),
        config.intent.as_ref(),
        sub_args.manifest_path.as_deref().map(Path::new),
    ) {
        Ok(intent) => intent,
        Err(message) => {
            eprintln!("targo trust: error: {message}");
            return ExitCode::from(2);
        }
    };
    if let Some(intent) = &repair_intent {
        eprintln!(
            "  Intent input: {} ({} bytes) — guiding AI repair prompts",
            intent.source.label(),
            intent.text.len()
        );
    }
    let repair_intent_excerpt = repair_intent.as_ref().map(|intent| intent.excerpt(2000));

    let mut tracker = ConvergenceTracker::new(max_iterations);
    let mut backprop = BackpropEngine::with_protected(&config.skip_functions);
    let binary_source_provenance = match runtime_binary_source_provenance_for_rewrite_loop(sub_args)
    {
        Ok(source_provenance) => source_provenance,
        Err(message) => {
            eprintln!("targo trust: error: {message}");
            return ExitCode::from(2);
        }
    };

    let mut default_source_file: Option<String> = None;
    if sub_args.is_single_file {
        let file_path = std::fs::canonicalize(
            sub_args.single_file_path().expect("single-file mode should have a file path"),
        )
        .unwrap_or_else(|_| {
            PathBuf::from(
                sub_args.single_file_path().expect("single-file mode should have a file path"),
            )
        });
        let path_str = file_path.display().to_string();
        backprop.set_default_source_file(path_str.clone());
        default_source_file = Some(path_str);
    }

    let loop_start = Instant::now();
    let mut last_frontier = ProofFrontier { proved: 0, failed: 0, unknown: 0 };
    let mut last_success = false;
    // Whether the frontier `last_success` judged is a measurement (T7b).
    let mut last_outcome = trust_types::determinism::UnitOutcome::Measured;
    let mut last_decision = LoopDecision::Continue { verdict: "starting" };
    let mut repair_iterations = Vec::new();
    // Edits that are on disk and still owe the compiler a verdict. At most one
    // generation is ever outstanding: the loop judges it before writing more.
    let mut unverified: Option<UnverifiedRewrites> = None;
    // Set when an undo could not be completed, which is the one state where the
    // tree holds content neither the user nor a judged rewrite produced.
    let mut restore_failed = false;

    eprintln!();
    eprintln!("targo trust: starting rewrite loop (max {} iterations)", max_iterations);

    for iteration in 0..max_iterations {
        let iter_start = Instant::now();
        let mut halted_by_rejection = None;
        print_iteration_header(iteration, max_iterations);

        // Step 1: Prove -- run the compiler and capture results.
        let (cmd_args, run_result) = match rewrite_loop_prove_once(
            rustc,
            subcommand,
            sub_args,
            config,
            selected_codegen_backend,
            supports_json_transport,
            iteration > 0,
        ) {
            Ok(captured) => captured,
            Err(exit_code) => return exit_code,
        };

        // Step 2b: Backprop AI prompt -- for every Failed/Unknown obligation,
        // print an explicit AI prompt asking the assistant to add the strongest
        // `#[requires]`/`#[ensures]` to repair the failing function. The prompt
        // is paired with a `claude --dangerously-skip-permissions` invocation
        // so the operator can pipe it straight in.
        print_ai_repair_prompts_for_results(
            &run_result.verification_results,
            default_source_file.as_deref(),
            repair_intent_excerpt.as_deref(),
        );

        if let Some(gap) = hardened_proof_gate_failure_for_results(
            crate::pipeline::hardened::HardenedProofGateInput {
                results: &run_result.verification_results,
                compiler_diagnostics: &run_result.compiler_diagnostics,
                report_subject: &run_result.report_subject,
                zero_obligation_functions: &run_result.zero_obligation_functions,
                test_harness_exclusions: &run_result.test_harness_exclusions,
                live_transport_authority: Some(&run_result.live_transport_authority),
                config,
                hardened: sub_args.hardened,
                trust_profile: sub_args.trust_profile.as_deref(),
            },
        ) {
            eprintln!(
                "targo trust: hardened proof evidence gate failed in rewrite loop: {}/{} hardened obligations have publishable native proof evidence",
                gap.proof_evidence_entries, gap.hardened_obligations
            );
            return ExitCode::FAILURE;
        }

        let binary_source_blockers = binary_source_backpropagation_blockers(
            &run_result.verification_results,
            binary_source_provenance.as_ref(),
        );
        if !binary_source_blockers.is_empty() {
            print_runtime_binary_source_backpropagation_blocker(&binary_source_blockers);
            return ExitCode::FAILURE;
        }

        // Step 2: Strengthen -- analyze failures and propose rewrites.
        let obligations = run_result.verification_results.len();
        let frontier = ProofFrontier::from_results(&run_result.verification_results);
        let iteration_success = rewrite_iteration_success(
            run_result.exit_code,
            &run_result.verification_results,
            &run_result.zero_obligation_functions,
            &run_result.test_harness_exclusions,
            run_result.coverage.as_ref(),
            &run_result.missing_target_coverage,
            sub_args.strict_artifact_policy(),
        );
        let strengthen = strengthen_failures_with_binary_source_provenance(
            &run_result.verification_results,
            binary_source_provenance.as_ref(),
        );
        let proposal_summaries = strengthen.summaries();

        // Step 3: Converge -- judge what this run measured. The verdict comes
        // before the next edit is written, because this same run is the first
        // and only judgement on the edits the previous iteration made: deciding
        // after applying would stack an unjudged generation on top of a
        // generation already known to be bad.
        let decision = tracker.observe(frontier.clone());
        print_iteration_summary(&frontier, &proposal_summaries, &decision, &iter_start.elapsed());

        // Step 4: Adjudicate the outstanding edits against that verdict, and
        // take them back if they did not earn their place.
        if let Some(pending) = unverified.take() {
            // Taking the generation out is the accept: without a rejection its
            // checkpoint has done its job and the edits stand.
            if let Some(rejection) = rewrite_rejection(run_result.exit_code, obligations, &decision)
            {
                eprintln!("{}", describe_restore(&pending, rejection));
                match pending.restore() {
                    Ok(files) => {
                        eprintln!("  Restored {files} file(s) to their pre-rewrite content.");
                    }
                    Err(error) => {
                        // The tree now holds content neither we nor the user
                        // authored. Say so loudly and stop touching it.
                        eprintln!(
                            "targo trust: error: could not restore the pre-rewrite source: {error}"
                        );
                        eprintln!(
                            "targo trust: the working tree holds ungraded rewrites -- inspect it before rebuilding."
                        );
                        restore_failed = true;
                    }
                }
                halted_by_rejection = Some(rejection);
            }
        }

        // Step 5: Backprop -- apply rewrites to source via trust-backprop, but
        // only while the loop is still moving forward.
        let mut bp_result = BackpropResult::nothing_applied(0, 0);
        let keep_rewriting = halted_by_rejection.is_none()
            && !restore_failed
            && !iteration_success
            && matches!(decision, LoopDecision::Continue { .. });
        if keep_rewriting && !strengthen.proposals.is_empty() {
            bp_result = backprop.apply_strengthen_proposals(&strengthen.proposals, 0, 0);
            eprintln!(
                "  Backprop: {} rewrites applied to {} files ({} governance skips, {} limit skips, {} queued for review)",
                bp_result.rewrites_applied,
                bp_result.files_modified,
                bp_result.governance_skips,
                bp_result.limit_skips,
                bp_result.pending_rewrites.len(),
            );
            if let Some(checkpoint) = bp_result.pre_apply_checkpoint.take() {
                unverified =
                    UnverifiedRewrites::new(iteration + 1, checkpoint, bp_result.rewrites_applied);
            }
        }
        let iter_elapsed = iter_start.elapsed();

        let proposal_records = strengthen.proposal_records();
        let rewrite_records = build_rewrite_records(
            &bp_result.applied_rewrites,
            &bp_result.pending_rewrites,
            &bp_result.file_results,
        );
        append_audit_entries(&mut audit_trail, iteration + 1, &rewrite_records);
        repair_iterations.push(RepairIteration {
            iteration: iteration + 1,
            command: cmd_args,
            exit_code: run_result.exit_code,
            frontier: frontier.clone(),
            results: run_result.verification_results.clone(),
            compiler_diagnostics: run_result.compiler_diagnostics,
            failures: strengthen.failures,
            proposals: proposal_records,
            applied_rewrites: bp_result.applied_rewrites.clone(),
            pending_rewrites: bp_result.pending_rewrites.clone(),
            rewrite_records,
            governance_skips: bp_result.governance_skips,
            limit_skips: bp_result.limit_skips,
            duration_ms: iter_elapsed.as_millis() as u64,
        });

        if let Some(rejection) = halted_by_rejection {
            // This run measured source that has just been reverted, so the
            // frontier the user is left with is the one before it.
            last_decision = LoopDecision::Regressed { reason: rejection.reason() };
            last_success = false;
            break;
        }
        last_frontier = frontier;
        last_success = iteration_success;
        last_outcome = run_result.outcome;
        last_decision = decision.clone();

        match &decision {
            LoopDecision::Continue { .. } => {
                if iteration_success {
                    eprintln!("  All obligations proved -- stopping early.");
                    last_decision = LoopDecision::Converged { stable_rounds: 1 };
                    break;
                }
                if strengthen.proposals.is_empty() {
                    if last_frontier.failed > 0 {
                        eprintln!(
                            "  No proposals generated for {} failures -- stopping.",
                            last_frontier.failed
                        );
                    } else {
                        eprintln!(
                            "  No proposals generated for incomplete proof frontier -- stopping."
                        );
                    }
                    break;
                }
            }
            LoopDecision::Converged { .. }
            | LoopDecision::Regressed { .. }
            | LoopDecision::IterationLimitReached => break,
        }
    }

    // Nothing may outlive the loop unjudged. The loop only writes a generation
    // when a later prove pass will grade it, which is why the last iteration
    // measures instead of editing; this is the fail-closed backstop for a future
    // change to that ordering, not a second verdict path. An edit nobody graded
    // goes back, and the run does not claim success either way.
    if let Some(pending) = unverified.take() {
        eprintln!();
        eprintln!(
            "targo trust: reverting {} rewrite(s) from iteration {} that no prove pass graded",
            pending.rewrites(),
            pending.iteration()
        );
        match pending.restore() {
            Ok(files) => eprintln!("  Restored {files} file(s) to their pre-rewrite content."),
            Err(error) => {
                eprintln!("targo trust: error: could not restore the pre-rewrite source: {error}");
                eprintln!(
                    "targo trust: the working tree holds ungraded rewrites -- inspect it before rebuilding."
                );
                restore_failed = true;
            }
        }
        last_success = false;
    }

    let total_elapsed = loop_start.elapsed();
    print_loop_summary(&tracker, &last_frontier, &total_elapsed, &last_decision);

    if let Some(dir) = sub_args.report_dir.as_deref() {
        let artifact = RepairArtifact {
            schema_version: "0.2.0",
            summary: RepairRunSummary {
                iterations: tracker.iteration_count(),
                succeeded: last_success,
                final_frontier: last_frontier.clone(),
                final_decision: decision_label(&last_decision),
                total_duration_ms: total_elapsed.as_millis() as u64,
                exact_source_type_ownership_artifact_digest: binary_source_provenance
                    .as_ref()
                    .and_then(|provenance| provenance.exact_source_type_ownership_artifact_digest())
                    .map(str::to_string),
            },
            iterations: repair_iterations,
            audit_trail,
        };
        let output_dir = Path::new(dir);
        match write_repair_artifact(output_dir, &artifact) {
            Ok(()) => eprintln!("targo trust: wrote {dir}/repair.json"),
            Err(e) => eprintln!("targo trust: failed to write repair artifact: {e}"),
        }
        match write_repair_markdown(output_dir, &artifact) {
            Ok(()) => eprintln!("targo trust: wrote {dir}/repair.md"),
            Err(e) => eprintln!("targo trust: failed to write repair markdown: {e}"),
        }
    }

    rewrite_loop_exit(last_success && !restore_failed, last_outcome)
}

/// The rewrite loop's exit. A tree left holding rewrites that could neither
/// be judged nor undone is a failed run whatever the last frontier said, so
/// the caller folds that into `succeeded`. A loop that converged on rows that
/// are no measurement (T7b: outcome `could-not-run` or `not-reproducible`)
/// claims no pass: it could not run (3). Any other loop that did not converge
/// exits 1, as before.
fn rewrite_loop_exit(succeeded: bool, outcome: trust_types::determinism::UnitOutcome) -> ExitCode {
    if !succeeded {
        return ExitCode::FAILURE;
    }
    if outcome != trust_types::determinism::UnitOutcome::Measured {
        eprintln!(
            "targo trust: COULD NOT RUN: the rewrite loop's final frontier is no measurement \
             (outcome {outcome}), so its pass is not one"
        );
        return ExitCode::from(crate::determinism_report::EXIT_COULD_NOT_RUN);
    }
    ExitCode::SUCCESS
}

pub(super) fn rewrite_iteration_success(
    compiler_exit: i32,
    results: &[VerificationResult],
    zero_obligation_functions: &[String],
    test_harness_exclusions: &[trust_types::GateExclusionReport],
    coverage: Option<&trust_types::VerificationCoverage>,
    missing_target_coverage: &[CargoTargetIdentity],
    require_coverage: bool,
) -> bool {
    let (counts, _transport_defects) = partition_outcome_counts(results);
    // Trust (completeness-gap ruling, 2026-07-25): the rewrite loop is a
    // CONVERGENCE criterion, not a build gate, so it keeps the full-discharge
    // predicate (`GateLane::Certify`) rather than following the relaxed default.
    // The loop exists to drive code to a statically proved state; accepting a
    // `runtime_checked` row would declare success on exactly the gap it is trying
    // to close, and it would stop iterating one step early. Its original
    // assertions — runtime-checked is NOT success — are preserved verbatim by
    // this lane.
    let excluded_functions = test_harness_exclusions
        .iter()
        .map(|exclusion| exclusion.function.clone())
        .collect::<Vec<_>>();
    evaluate_run_gate(
        GateLane::Certify,
        compiler_exit,
        counts,
        coverage,
        !missing_target_coverage.is_empty(),
        require_coverage,
        zero_obligation_functions,
        &excluded_functions,
    )
    .is_success()
}

fn coverage_accounting_overflowed(rows: &[trust_types::CoverageTransportSummary]) -> bool {
    fn overflows(mut values: impl Iterator<Item = usize>) -> bool {
        values.try_fold(0usize, |total, value| total.checked_add(value)).is_none()
    }

    overflows(rows.iter().map(|row| row.eligible))
        || overflows(rows.iter().map(|row| row.processed))
}

#[cfg(test)]
fn cargo_test_execution_evidence_blocker(
    compile_succeeded: bool,
    missing_transport: Option<&str>,
    strict_artifact_policy: bool,
    coverage: Option<&trust_types::VerificationCoverage>,
    coverage_overflowed: bool,
    missing_target_coverage: &[CargoTargetIdentity],
) -> Option<String> {
    if !compile_succeeded {
        return Some("Cargo test compile-only phase failed".to_string());
    }
    if let Some(reason) = missing_transport {
        return Some(reason.to_string());
    }
    if strict_artifact_policy
        && (coverage_overflowed
            || coverage.is_none_or(|coverage| !coverage.coverage_complete)
            || !missing_target_coverage.is_empty())
    {
        return Some(
            "strict authenticated coverage was incomplete after the Cargo test compile-only phase"
                .to_string(),
        );
    }
    None
}

#[cfg(test)]
mod selection_and_control_tests {
    use std::path::{Path, PathBuf};

    use sha2::Digest as _;

    #[cfg(unix)]
    use super::TRUSTD_DISABLE_ENV;
    use super::{
        CertifiedTestExecutionCompletionScope, CertifiedTestExecutionPhaseState,
        CertifiedTestExecutionReport, ChildSetupError, LaneFlagsInput, ProjectRequirementFlags,
        SessionLease, TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV,
        TRUST_TARGO_LANE_RUSTFLAGS_ENV, TrustPolicySelection, VerificationControls,
        VerificationSession, append_verification_control_args, apply_cargo_child_rustc_env,
        apply_crate_memory_coordination_with, apply_lane_flags_env, apply_memory_aware_job_bound,
        apply_targo_test_monitor_session, canonical_rustc_option_name,
        cargo_args_with_proof_message_format, cargo_config_dirs_select_jobs,
        cargo_config_search_selects_jobs, cargo_config_text_selects_jobs,
        cargo_jobs_explicitly_selected_with, cargo_manifest_path_arg, cargo_target_dir,
        cargo_target_dir_arg, cargo_test_compile_only_args, cargo_test_execution_evidence_blocker,
        cargo_test_retained_args, certified_test_execution_platform_blocker,
        certified_test_execution_platform_blocker_for, child_signal_exit_code, child_status_code,
        configured_verified_cargo_child_with_memory, encode_lane_rustflags, env,
        inherited_trust_rustflags_warning, prepare_ephemeral_single_file_output,
        record_certified_test_execution_error, scrub_proof_compiler_authority_env,
        selected_package_names_from_selection, temp_single_file_output_path,
        trust_verify_disable_diagnostic, validate_direct_custom_target_extension_tcb,
        verification_cache_target_dir, verification_control_options, verified_lane_flags,
        write_test_execution_authority,
    };
    use crate::config::TrustConfig;
    use crate::pipeline::transport::{CargoTargetIdentity, CargoTestExecutable};
    use crate::pipeline::{ResolvedCargoPackage, ResolvedCargoSelection};

    /// The built-in budget profile, for control fixtures.
    static BUILTIN_BUDGET: std::sync::LazyLock<trust_types::determinism::BudgetProfile> =
        std::sync::LazyLock::new(trust_types::determinism::BudgetProfile::builtin);

    fn s(args: &[&str]) -> Vec<String> {
        args.iter().map(|a| a.to_string()).collect()
    }

    /// Both branches of the injection, exercised without depending on the
    /// ambient Cargo configuration of whatever tree the tests run in.
    #[test]
    fn memory_aware_job_bound_is_injected_only_when_the_operator_chose_nothing() {
        let mut args = s(&["--workspace", "--all-targets"]);
        apply_memory_aware_job_bound(&mut args, false, 9);
        assert_eq!(args, s(&["--workspace", "--all-targets", "-j", "9"]));

        // Before the `--` separator, so the job count reaches Cargo and not
        // the test binary.
        let mut args = s(&["--workspace", "--", "--nocapture"]);
        apply_memory_aware_job_bound(&mut args, false, 3);
        assert_eq!(args, s(&["--workspace", "-j", "3", "--", "--nocapture"]));

        // An operator selection suppresses it outright rather than being
        // appended after and silently outranked by Cargo's last-wins parse.
        let mut args = s(&["--workspace", "-j", "2"]);
        apply_memory_aware_job_bound(&mut args, true, 9);
        assert_eq!(
            args,
            s(&["--workspace", "-j", "2"]),
            "an operator job count must survive alone"
        );

        let mut args = s(&["--workspace"]);
        apply_memory_aware_job_bound(&mut args, true, 9);
        assert_eq!(
            args,
            s(&["--workspace"]),
            "a config-file or environment selection must suppress the injection too"
        );
    }

    /// An operator's explicit job count must suppress the memory-aware
    /// injection outright. The injected `-j` is spliced in before the `--`
    /// separator, i.e. after the operator's own flags, so Cargo's last-wins
    /// parsing would silently outrank it.
    #[test]
    fn explicit_cargo_job_selection_is_detected_in_every_spelling() {
        for args in [
            s(&["--workspace", "-j", "4"]),
            s(&["--workspace", "-j4"]),
            s(&["--workspace", "-j=4"]),
            s(&["--workspace", "--jobs", "4"]),
            s(&["--workspace", "--jobs=4"]),
            s(&["-j", "1", "--", "--nocapture"]),
        ] {
            assert!(
                cargo_jobs_explicitly_selected_with(&args, None, false),
                "operator job selection went undetected in {args:?}"
            );
        }
    }

    /// Nothing else may be mistaken for a job selection, and a `-j` that
    /// belongs to the test binary after `--` is not Cargo's.
    #[test]
    fn absent_cargo_job_selection_leaves_the_memory_aware_default_in_charge() {
        for args in [
            s(&[]),
            s(&["--workspace", "--all-targets", "--all-features", "--locked"]),
            s(&["--", "-j", "4"]),
            s(&["--", "--jobs=4"]),
        ] {
            assert!(
                !cargo_jobs_explicitly_selected_with(&args, None, false),
                "a memory-aware job count was suppressed by {args:?}"
            );
        }
    }

    /// Cargo honors `CARGO_BUILD_JOBS`, so it is an operator override too; an
    /// injected `-j` on the command line would outrank it.
    #[test]
    fn cargo_build_jobs_environment_counts_as_an_operator_override() {
        let args = s(&["--workspace"]);
        assert!(cargo_jobs_explicitly_selected_with(&args, Some(std::ffi::OsStr::new("4")), false));
        assert!(
            !cargo_jobs_explicitly_selected_with(&args, Some(std::ffi::OsStr::new("")), false),
            "an empty CARGO_BUILD_JOBS selects nothing and must not suppress the clamp"
        );
        assert!(!cargo_jobs_explicitly_selected_with(&args, None, false));
    }

    /// `[build] jobs` in a Cargo config file is an operator selection that a
    /// command-line `-j` outranks, so injecting one would silently widen the
    /// gate past what the config asked for. This repository's own
    /// `.cargo/config.toml` sets it.
    #[test]
    fn cargo_config_build_jobs_counts_as_an_operator_override() {
        let args = s(&["--workspace"]);
        assert!(cargo_jobs_explicitly_selected_with(&args, None, true));
    }

    /// The config scan must find `build.jobs` in the spellings Cargo accepts
    /// and must not fire on anything else — including a `jobs` key belonging
    /// to some other table, which is the mistake a bare substring search makes.
    #[test]
    fn cargo_config_text_scan_finds_build_jobs_without_over_matching() {
        // The real text of this repository's own config, reduced.
        let repo_config =
            "# comment\n[build]\n# Spark shares its 128 GiB pool.\njobs = 4\n\n[env]\nX = \"1\"\n";
        for selecting in [
            repo_config,
            "[build]\njobs=4\n",
            "[build]\n  jobs  =  4\n",
            "[build]\n\"jobs\" = 4\n",
            "build.jobs = 2\n",
            "[target.x86_64-apple-darwin]\nrustflags = []\n[build]\njobs = 1\n",
        ] {
            assert!(
                cargo_config_text_selects_jobs(selecting),
                "config scan missed a job selection in {selecting:?}"
            );
        }
        for quiet in [
            "",
            "[build]\nincremental = true\n",
            "[build]\n# jobs = 4\n",
            "[alias]\njobs = \"build\"\n",
            "[build]\ntarget = \"x\"\n[env]\njobs = \"4\"\n",
            "[net]\nretry = 2\n",
        ] {
            assert!(
                !cargo_config_text_selects_jobs(quiet),
                "config scan invented a job selection in {quiet:?}"
            );
        }
    }

    /// Cargo reads `.cargo/config.toml` from the invocation directory and
    /// every ancestor, then `$CARGO_HOME`. All of those are the operator.
    #[test]
    fn cargo_config_search_walks_ancestors_and_cargo_home() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock should be after epoch")
            .as_nanos();
        let container = std::env::temp_dir()
            .join(format!("targo-trust-cargo-config-jobs-{}-{unique}", std::process::id()));
        let root = container.join("fixture");
        let nested = root.join("workspace").join("crates").join("leaf");
        std::fs::create_dir_all(&nested).expect("should create nested dirs");
        let home = root.join("cargo-home");
        std::fs::create_dir_all(&home).expect("should create cargo home");
        let selects_jobs = |home: Option<&Path>| {
            cargo_config_dirs_select_jobs(
                nested.ancestors().take_while(|dir| dir.starts_with(&root)),
                home,
            )
        };

        // Model a real config outside the fixture. The production walk must
        // still honor it, while fixture negatives read only owned ancestors.
        let outside_cargo = container.join(".cargo");
        std::fs::create_dir_all(&outside_cargo).expect("should create outside config dir");
        std::fs::write(outside_cargo.join("config.toml"), "[build]\njobs = 3\n")
            .expect("should write outside config");
        assert!(cargo_config_search_selects_jobs(&nested, None));

        assert!(!selects_jobs(Some(&home)), "an empty tree selects no job count");

        // An ancestor's config counts.
        let ancestor_cargo = root.join("workspace").join(".cargo");
        std::fs::create_dir_all(&ancestor_cargo).expect("should create .cargo");
        std::fs::write(ancestor_cargo.join("config.toml"), "[build]\njobs = 4\n")
            .expect("should write config");
        assert!(selects_jobs(Some(&home)));

        // ... and so does the legacy extensionless name, and $CARGO_HOME.
        std::fs::remove_file(ancestor_cargo.join("config.toml")).expect("should remove config");
        std::fs::write(ancestor_cargo.join("config"), "[build]\njobs = 4\n")
            .expect("should write legacy config");
        assert!(selects_jobs(Some(&home)));

        std::fs::remove_file(ancestor_cargo.join("config")).expect("should remove config");
        assert!(!selects_jobs(Some(&home)));
        std::fs::write(home.join("config.toml"), "[build]\njobs = 2\n")
            .expect("should write cargo home config");
        assert!(selects_jobs(Some(&home)));
        assert!(!selects_jobs(None), "without a CARGO_HOME there is nothing left to find");

        std::fs::remove_dir_all(&container).expect("should remove temp dir");
    }

    #[test]
    fn certified_test_execution_platform_gate_matches_the_current_authenticated_backend() {
        let blocker = certified_test_execution_platform_blocker();
        if cfg!(any(
            all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")),
            all(target_os = "macos", any(target_arch = "x86_64", target_arch = "aarch64"))
        )) {
            assert!(blocker.is_none(), "supported host was blocked: {blocker:?}");
        } else {
            assert!(
                blocker.is_some_and(|message| {
                    message.contains("requires Linux sealed-memfd execveat or macOS suspended")
                }),
                "unsupported host did not fail closed: {blocker:?}"
            );
        }
    }

    #[test]
    fn certified_test_execution_platform_gate_matches_cargo_target_matrix() {
        for (target_os, target_arch) in
            [("linux", "x86_64"), ("linux", "aarch64"), ("macos", "x86_64"), ("macos", "aarch64")]
        {
            assert_eq!(
                certified_test_execution_platform_blocker_for(target_os, target_arch),
                None,
                "{target_os}-{target_arch} has an authenticated Cargo launch backend"
            );
        }

        for (target_os, target_arch) in [
            ("linux", "x86"),
            ("linux", "powerpc64"),
            ("macos", "x86"),
            ("macos", "powerpc64"),
            ("windows", "x86_64"),
            ("freebsd", "aarch64"),
        ] {
            let blocker = certified_test_execution_platform_blocker_for(target_os, target_arch);
            assert!(
                blocker.is_some_and(|message| {
                    message.contains("no implemented authenticated launch backend")
                }),
                "{target_os}-{target_arch} must fail closed: {blocker:?}"
            );
        }
    }

    #[test]
    fn certified_test_pre_spawn_error_remains_blocked_in_the_typed_report() {
        let mut report = CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::Blocked,
            blocker: None,
            phase_b_exit: None,
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        };
        record_certified_test_execution_error(
            Some(&mut report),
            false,
            "unsupported immutable execution handle",
        );
        assert_eq!(report.phase_b_state, CertifiedTestExecutionPhaseState::Blocked);
        assert_eq!(report.blocker.as_deref(), Some("unsupported immutable execution handle"));
        assert_eq!(report.phase_b_exit, None, "no phase-B Cargo child was started");
    }

    #[test]
    fn certified_test_cargo_child_installs_or_removes_the_complete_authority_tuple() {
        let session = VerificationSession::create().expect("create verification session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: None,
        };
        let selection = ResolvedCargoSelection {
            packages: Vec::new(),
            resolved_packages: std::collections::BTreeSet::new(),
            target_directory: session.artifact_root().join("target"),
        };
        let authority_path = session.artifact_root().join("execution-authority.json");
        let authority_sha256 = "0123456789abcdef".repeat(4);
        let args = s(&["test", "--tests"]);
        let rustc = std::path::Path::new("/authenticated/toolchain/bin/trustc");

        let bound = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &ProjectRequirementFlags::default(),
            &selection,
            true,
            Some((&authority_path, &authority_sha256)),
            |command, _, _| {
                command.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
                command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/test/trustd.sock");
                Ok(())
            },
        )
        .expect("configure authenticated phase-B Cargo child");
        for (name, expected) in [
            ("TRUST_TARGO_PREPARED_TEST_SESSION", std::ffi::OsStr::new(&session.id)),
            ("TRUST_TARGO_TEST_EXECUTION_MANIFEST", authority_path.as_os_str()),
            ("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256", std::ffi::OsStr::new(&authority_sha256)),
        ] {
            assert_eq!(
                bound
                    .get_envs()
                    .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                    .map(|(_, value)| value),
                Some(Some(expected)),
                "phase-B Cargo child did not receive exact `{name}` authority"
            );
        }

        let unbound = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &ProjectRequirementFlags::default(),
            &selection,
            true,
            None,
            |command, _, _| {
                command.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
                command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/test/trustd.sock");
                Ok(())
            },
        )
        .expect("configure Cargo child without execution authority");
        for name in [
            "TRUST_TARGO_PREPARED_TEST_SESSION",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        ] {
            assert_eq!(
                unbound
                    .get_envs()
                    .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                    .map(|(_, value)| value),
                Some(None),
                "unbound Cargo child did not explicitly remove `{name}`"
            );
        }
    }

    /// Trust (v6/D1): the spec-goal artifact transport. A requested emission
    /// stages the exact directory on the Cargo child; an unrequested run
    /// explicitly SCRUBS any inherited value (the ambient-authority scrub owns
    /// `TRUST_SPEC_EMIT_DIR`), so ambient shell state can never pick where a
    /// verified run writes evidence.
    #[test]
    fn spec_emit_dir_is_staged_exactly_when_requested_and_scrubbed_otherwise() {
        let session = VerificationSession::create().expect("create verification session");
        let spec_dir = session.artifact_root().join("spec-clean");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: Some(&spec_dir),
        };
        let selection = ResolvedCargoSelection {
            packages: Vec::new(),
            resolved_packages: std::collections::BTreeSet::new(),
            target_directory: session.artifact_root().join("target"),
        };
        let args = s(&["check"]);
        let rustc = std::path::Path::new("/authenticated/toolchain/bin/trustc");
        let configure =
            |command: &mut std::process::Command, _: &[String], _: Option<&std::path::Path>| {
                command.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
                Ok(())
            };

        let requested = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &ProjectRequirementFlags::default(),
            &selection,
            false,
            None,
            configure,
        )
        .expect("configure spec-emitting Cargo child");
        assert_eq!(
            requested
                .get_envs()
                .find(|(key, _)| *key == std::ffi::OsStr::new("TRUST_SPEC_EMIT_DIR"))
                .map(|(_, value)| value),
            Some(Some(spec_dir.as_os_str())),
            "a requested emission must stage the exact session directory"
        );

        let unrequested = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &VerificationControls { spec_emit_dir: None, ..controls },
            &ProjectRequirementFlags::default(),
            &selection,
            false,
            None,
            configure,
        )
        .expect("configure Cargo child without spec emission");
        assert_eq!(
            unrequested
                .get_envs()
                .find(|(key, _)| *key == std::ffi::OsStr::new("TRUST_SPEC_EMIT_DIR"))
                .map(|(_, value)| value),
            Some(None),
            "an unrequested run must explicitly scrub inherited TRUST_SPEC_EMIT_DIR"
        );
    }

    #[test]
    fn proof_message_format_is_one_authenticated_json_stream_before_passthrough() {
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&[
                "test",
                "--message-format=json-render-diagnostics",
                "--message-format",
                "short",
                "--",
                "--nocapture",
            ]))
            .expect("canonical proof format"),
            s(&["test", "--message-format=json", "--", "--nocapture"]),
        );
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&["build"])).expect("insert proof format"),
            s(&["build", "--message-format=json"]),
        );
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&["build", "--message-format", "--release",]))
                .expect_err("an option cannot be consumed as the format value"),
            "--message-format requires a value",
        );
    }

    #[test]
    fn retained_test_args_preserve_compile_inventory_harness_args_and_exclude_doctests() {
        let original =
            s(&["test", "--release", "name_filter", "--message-format=short", "--", "--nocapture"]);
        assert_eq!(
            cargo_test_compile_only_args(&original).expect("compile phase"),
            s(&[
                "test",
                "--release",
                "name_filter",
                "--no-run",
                "--message-format=json",
                "--",
                "--nocapture",
            ])
        );
        #[cfg(unix)]
        assert_eq!(
            cargo_test_retained_args(&original).expect("retained compile phase"),
            s(&[
                "test",
                "--release",
                "name_filter",
                "--no-run",
                "--message-format=json",
                "--__retained-test-session",
                "--",
                "--nocapture"
            ])
        );

        let selected = s(&["test", "--test", "integration", "--", "--exact"]);
        assert_eq!(
            cargo_test_compile_only_args(&selected).expect("selected compile phase"),
            s(&[
                "test",
                "--test",
                "integration",
                "--no-run",
                "--message-format=json",
                "--",
                "--exact",
            ])
        );
        assert!(
            cargo_test_compile_only_args(&s(&["test", "--doc"]))
                .expect_err("doctest must fail closed")
                .contains("cannot precompile")
        );
        #[cfg(unix)]
        {
            let opaque = s(&["test", "--", "--skip", "--__retained-test-session"]);
            let retained = cargo_test_retained_args(&opaque).expect("opaque harness value");
            let separator = retained.iter().position(|arg| arg == "--").unwrap();
            assert_eq!(&retained[separator + 1..], &["--skip", "--__retained-test-session"]);
            assert_eq!(
                retained[..separator]
                    .iter()
                    .filter(|arg| arg.as_str() == "--__retained-test-session")
                    .count(),
                1
            );
            assert!(
                cargo_test_retained_args(&s(&["test", "--__retained-test-session"]))
                    .expect_err("callers cannot select the internal endpoint")
                    .contains("owned")
            );
            assert!(
                cargo_test_retained_args(&s(&["test", "--no-run"]))
                    .expect_err("compile-only cannot receive a grant")
                    .contains("compile-only")
            );
            assert!(
                cargo_test_retained_args(&s(&["test", "--doc"]))
                    .expect_err("doctest must fail closed")
                    .contains("cannot precompile")
            );
        }
    }

    #[test]
    fn cargo_test_execution_requires_complete_structural_evidence() {
        let complete = trust_types::VerificationCoverage::from_counts(2, 2);
        let incomplete = trust_types::VerificationCoverage::from_counts(2, 1);
        assert!(
            cargo_test_execution_evidence_blocker(false, None, false, None, false, &[]).is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(
                true,
                Some("missing authenticated transport"),
                false,
                None,
                false,
                &[],
            )
            .is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, None, false, &[]).is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&incomplete), false, &[],)
                .is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&complete), true, &[],)
                .is_some()
        );
        assert_eq!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&complete), false, &[],),
            None
        );
        assert_eq!(
            cargo_test_execution_evidence_blocker(true, None, false, None, false, &[]),
            None,
            "advisory policy still requires transport but does not claim strict coverage"
        );
    }

    #[test]
    fn preexecution_structural_success_does_not_qualify_a_rejected_proof_lane() {
        let coverage = trust_types::VerificationCoverage::from_counts(1, 1);
        assert_eq!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&coverage), false, &[]),
            None,
            "the former pre-execution blocker only checked structural completeness"
        );
        let decision = super::evaluate_run_gate(
            super::GateLane::Certify,
            0,
            super::OutcomeCounts { total: 1, runtime_checked: 1, ..Default::default() },
            Some(&coverage),
            false,
            true,
            &[],
            &[],
        );
        assert!(!decision.is_success(), "runtime checking cannot satisfy --certify");
    }

    #[cfg(unix)]
    #[test]
    fn prepared_test_authorization_checks_native_digest_and_current_artifacts() {
        use trust_test_execution::{
            PLAN_SCHEMA, PreparedTest, PreparedTests, PreparedTestsReceipt, RECEIPT_SCHEMA,
        };
        let session = super::VerificationSession::create().unwrap();
        let target = tempfile::tempdir().unwrap();
        let executable = target.path().join("test");
        std::fs::write(&executable, b"test-image").unwrap();
        let path = executable.to_str().unwrap().to_owned();
        let sha256 = format!("{:x}", sha2::Sha256::digest(b"test-image"));
        let entries = vec![super::TestExecutionAuthorityEntry {
            target: "test".into(),
            path: path.clone(),
            sha256: sha256.clone(),
            size: 10,
        }];
        let mut plan = PreparedTests {
            schema: PLAN_SCHEMA.into(),
            session: session.id.clone(),
            host_os: std::env::consts::OS.into(),
            host_arch: std::env::consts::ARCH.into(),
            target_directory: target.path().to_str().unwrap().into(),
            no_fail_fast: false,
            tests: vec![PreparedTest {
                target: "test".into(),
                executable: path,
                sha256,
                size: 10,
                cwd: target.path().to_str().unwrap().into(),
                args: Vec::new(),
                env: Default::default(),
                results: None,
            }],
        };
        let plan_path = session.artifact_root().join("prepared-tests.json");
        let bytes = serde_json::to_vec(&plan).unwrap();
        std::fs::write(&plan_path, &bytes).unwrap();
        let mut receipt = PreparedTestsReceipt {
            schema: RECEIPT_SCHEMA.into(),
            session: session.id.clone(),
            path: plan_path.to_str().unwrap().into(),
            sha256: format!("{:x}", sha2::Sha256::digest(&bytes)),
        };
        assert!(
            super::load_prepared_tests(
                &session,
                target.path().to_str().unwrap(),
                &entries,
                Some(&receipt)
            )
            .is_ok()
        );
        std::fs::write(&plan_path, b"modified").unwrap();
        assert!(
            super::load_prepared_tests(
                &session,
                target.path().to_str().unwrap(),
                &entries,
                Some(&receipt)
            )
            .is_err()
        );
        plan.tests[0].env.insert("LD_PRELOAD".into(), "hostile".into());
        let bytes = serde_json::to_vec(&plan).unwrap();
        std::fs::write(&plan_path, &bytes).unwrap();
        receipt.sha256 = format!("{:x}", sha2::Sha256::digest(&bytes));
        assert!(
            super::load_prepared_tests(
                &session,
                target.path().to_str().unwrap(),
                &entries,
                Some(&receipt)
            )
            .is_err()
        );
    }

    #[test]
    fn test_execution_authority_binds_exact_private_executable_inventory() {
        use std::os::unix::fs::PermissionsExt as _;

        let target_root = tempfile::tempdir().expect("target directory");
        let toolchain_root = tempfile::tempdir().expect("toolchain directory");
        let executable = target_root.path().join("fixture-test");
        std::fs::write(&executable, b"authenticated test bytes").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755))
            .expect("mark executable");
        let target = CargoTargetIdentity {
            package_id: "path+file:///fixture#demo@0.1.0".to_string(),
            package_name: "demo".to_string(),
            target_name: "fixture".to_string(),
            target_kinds: vec!["test".to_string()],
            compile_target: "host".to_string(),
            compile_mode: "test".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: "c".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "test".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: "a".repeat(64),
        };
        let inventory = [CargoTestExecutable {
            target: target.clone(),
            path: executable.canonicalize().expect("canonical executable"),
            phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"authenticated test bytes")),
        }]
        .into_iter()
        .collect();
        let session = VerificationSession::create().expect("verification session");
        let manifest = write_test_execution_authority(
            &super::QualifiedTestExecution::for_authority_writer_test(&session.id),
            &session,
            target_root.path(),
            toolchain_root.path(),
            &inventory,
            None,
        )
        .expect("write execution authority");
        let metadata = std::fs::symlink_metadata(&manifest.path).expect("manifest metadata");
        assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
        let value: serde_json::Value = serde_json::from_slice(
            &std::fs::read(&manifest.path).expect("read execution authority"),
        )
        .expect("parse execution authority");
        assert_eq!(value["schema"], "trust.targo-test-execution-authority.v2");
        assert_eq!(value["verification_session"], session.id);
        assert_eq!(value["executables"].as_array().map(Vec::len), Some(1));
        assert_eq!(value["executables"][0]["size"], 24);
        assert_eq!(value["executables"][0]["sha256"].as_str().map(str::len), Some(64));
        assert_eq!(
            manifest.inventory_sha256,
            format!(
                "{:x}",
                sha2::Sha256::digest(
                    std::fs::read(&manifest.path).expect("read bound execution authority")
                )
            ),
            "the digest passed to phase-B Cargo must bind the exact manifest bytes"
        );
        assert_eq!(manifest.executables.len(), 1);
        assert_eq!(
            manifest.target_directory,
            target_root.path().canonicalize().unwrap().to_str().unwrap()
        );

        let second = target_root.path().join("fixture-test-second");
        std::fs::write(&second, b"second authenticated test").expect("write second executable");
        std::fs::set_permissions(&second, std::fs::Permissions::from_mode(0o755))
            .expect("mark second executable");
        let ambiguous = [
            CargoTestExecutable {
                target: target.clone(),
                path: executable.canonicalize().expect("canonical executable"),
                phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"authenticated test bytes")),
            },
            CargoTestExecutable {
                target,
                path: second.canonicalize().expect("canonical second executable"),
                phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"second authenticated test")),
            },
        ]
        .into_iter()
        .collect();
        let second_session = VerificationSession::create().expect("second verification session");
        assert!(
            write_test_execution_authority(
                &super::QualifiedTestExecution::for_authority_writer_test(&second_session.id),
                &second_session,
                target_root.path(),
                toolchain_root.path(),
                &ambiguous,
                None,
            )
            .expect_err("one Cargo target cannot authorize two executable identities")
            .contains("ambiguous executable paths")
        );

        let overlapping_session =
            VerificationSession::create().expect("overlap verification session");
        assert!(
            write_test_execution_authority(
                &super::QualifiedTestExecution::for_authority_writer_test(&overlapping_session.id),
                &overlapping_session,
                target_root.path(),
                target_root.path(),
                &inventory,
                None,
            )
            .expect_err("project artifacts must never live inside the toolchain TCB")
            .contains("overlaps authenticated Trust toolchain root")
        );
    }

    #[cfg(unix)]
    #[test]
    fn compiler_process_guard_times_out_the_process_group() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "sleep 30 & wait"]);
        super::CompilerProcessGuard::configure(&mut command);
        let mut child = command.spawn().expect("spawn hanging compiler fixture");
        let mut guard = super::CompilerProcessGuard::start(
            child.id(),
            super::CompilerProcessBounds::flat(std::time::Duration::from_millis(100)),
        );
        let _ = super::wait_for_compiler_process(&mut child, &mut guard);
        let error = guard.finish().expect_err("timeout must fail");
        assert!(error.contains("silent-process bound"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn compiler_process_guard_reaps_background_descendants_before_leader() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "sleep 30 & printf '%s' \"$!\" >&2; exit 0"]);
        command.stderr(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let mut child = command.spawn().expect("spawn background compiler fixture");
        let stderr = child.stderr.take().expect("stderr pipe");
        let mut guard = super::CompilerProcessGuard::start(
            child.id(),
            super::CompilerProcessBounds::flat(std::time::Duration::from_secs(2)),
        );
        let _ = super::wait_for_compiler_process(&mut child, &mut guard).expect("wait compiler");
        guard.finish().expect("natural exit");
        let mut pid_text = String::new();
        std::io::Read::read_to_string(&mut std::io::BufReader::new(stderr), &mut pid_text)
            .expect("read pid");
        let pid: i32 = pid_text.parse().expect("numeric pid");
        // The process-group kill is synchronous, but the kernel may expose a
        // just-killed descendant briefly while its exit is being reaped.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while unsafe { libc::kill(pid, 0) } == 0 && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        assert_ne!(unsafe { libc::kill(pid, 0) }, 0, "background descendant survived");
    }

    #[cfg(any(unix, windows))]
    #[test]
    fn portable_compiler_process_leader_wait_enforces_deadline_and_reaps() {
        #[cfg(unix)]
        let mut command = {
            let mut command = std::process::Command::new("/bin/sh");
            command.args(["-c", "sleep 30"]);
            command
        };
        #[cfg(windows)]
        let mut command = {
            let mut command = std::process::Command::new("cmd.exe");
            command.args(["/C", "ping -n 30 127.0.0.1 >NUL"]);
            command
        };
        let mut child = command.spawn().expect("spawn hanging compiler leader fixture");
        let state = super::CompilerTimeoutState::new(
            child.id(),
            super::CompilerProcessBounds::flat(std::time::Duration::from_millis(100)),
        );
        let status = super::wait_for_compiler_leader_until(&mut child, &state)
            .expect("kill and reap compiler leader");
        assert!(state.timed_out());
        assert!(!status.success());
        assert!(child.try_wait().expect("query reaped child").is_some());
    }

    /// A live drain must not hide a timeout. Under the progress-sensitive
    /// guard that claim is strictly stronger than it used to be, because the
    /// drain now *feeds* the deadline: the fixture emits a burst of
    /// diagnostics straight into the parser and only then stalls, so the
    /// bytes this test delivers are exactly the bytes that could wrongly keep
    /// the process alive. The idle bound must still fire, the process group
    /// must still die, and the parser must still see EOF.
    #[cfg(any(unix, windows))]
    #[test]
    fn compiler_process_pipe_drain_does_not_hide_timeout() {
        #[cfg(unix)]
        let mut command = {
            let mut command = std::process::Command::new("/bin/sh");
            command.args([
                "-c",
                "i=0; while [ $i -lt 5 ]; do echo diagnostic >&2; sleep 0.05; i=$((i+1)); done; \
                 sleep 30 & wait",
            ]);
            command
        };
        #[cfg(windows)]
        let mut command = {
            let mut command = std::process::Command::new("cmd.exe");
            command.args(["/C", "echo diagnostic 1>&2 & ping -n 30 127.0.0.1 >NUL"]);
            command
        };
        command.stderr(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let started = std::time::Instant::now();
        let mut child = command.spawn().expect("spawn hanging compiler pipe fixture");
        let stderr = child.stderr.take().expect("compiler stderr pipe");
        // The silent bound is long enough that it cannot be what kills this:
        // only the idle bound, armed by the drained burst, can.
        let mut guard = super::CompilerProcessGuard::start(
            child.id(),
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_secs(30),
                idle: std::time::Duration::from_millis(400),
                absolute: std::time::Duration::from_secs(30),
            },
        );
        let output = super::spawn_compiler_stderr_parser(
            stderr,
            guard.progress(),
            false,
            false,
            false,
            String::new(),
            false,
        );

        let _ = super::wait_for_compiler_process(&mut child, &mut guard).expect("wait compiler");
        let error = guard.finish().expect_err("timeout must fail");
        assert!(error.contains("stopped making progress"), "{error}");
        assert!(error.contains("idle bound"), "{error}");
        super::receive_compiler_output(output, "test compiler stderr")
            .expect("killed compiler must close stderr");
        assert!(started.elapsed() < std::time::Duration::from_secs(5));
    }

    /// The defect this pair of tests exists for, stated once.
    ///
    /// ay 0.27.0's release gate (2026-09-18) compiled 323 units in 359m with
    /// zero failures, and was then discarded 39s after Cargo printed `Finished`
    /// because the Cargo stdout parser had not yet DELIVERED -- it had reached
    /// EOF and was working through ~150k retained TRUST_JSON transport lines.
    /// The guard's own message blamed "an uncontained descendant", a claim it
    /// had made no observation of. Both halves are asserted below: a slow parse
    /// after EOF must not fail, and a genuinely held write end must still fail
    /// AND name a holder.
    #[cfg(unix)]
    #[test]
    fn a_parse_that_outlives_the_close_bound_after_eof_still_succeeds() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "echo diagnostic"]);
        command.stdout(std::process::Stdio::piped());
        let mut child = command.spawn().expect("spawn closing fixture");
        let stdout = child.stdout.take().expect("fixture stdout pipe");

        let close_bound = std::time::Duration::from_millis(200);
        // Three times the bound, entirely AFTER the read loop has drained the
        // pipe to EOF -- the shape of the ay parse, compressed.
        let parse_after_eof = close_bound * 3;
        let (eof_sender, eof_receiver) = std::sync::mpsc::sync_channel(1);
        let (parse_sender, parse_receiver) = std::sync::mpsc::sync_channel(1);
        let channel = super::spawn_pipe_parser(
            stdout,
            std::sync::Arc::new(super::CompilerProgress::new()),
            move |mut reader| {
                let mut drained = String::new();
                std::io::Read::read_to_string(&mut reader, &mut drained)
                    .map_err(|error| error.to_string())?;
                eof_sender.send(()).map_err(|error| error.to_string())?;
                parse_receiver.recv().map_err(|error| error.to_string())?;
                std::thread::sleep(parse_after_eof);
                Ok(drained)
            },
        );

        let _ = child.wait().expect("reap closing fixture");
        eof_receiver.recv_timeout(std::time::Duration::from_secs(5)).expect("parser reached EOF");
        let started = std::time::Instant::now();
        parse_sender.send(()).expect("release parser after EOF");
        let parsed = super::receive_compiler_output_within(
            channel,
            "test cargo stdout",
            close_bound,
            super::POST_EOF_PARSE_LIVENESS_BOUND,
        )
        .expect("EOF discharges containment, so the parse must be allowed to finish");
        assert_eq!(parsed.trim(), "diagnostic");
        assert!(
            started.elapsed() >= parse_after_eof,
            "the wait must have outlasted the close bound rather than expiring at it: {:?}",
            started.elapsed()
        );
    }

    /// Unbounding the post-EOF wait would trade a bounded refusal for an
    /// unbounded hang, so it is not unbounded: a parser that neither returns
    /// nor unwinds still ends the run, at a bound far above any real parse.
    ///
    /// What that refusal may NOT do is blame a process. The pipe is shut; there
    /// is no holder; the fault is in this crate. The message has to say so, or
    /// the next person to read it will go hunting for a descendant that does
    /// not exist -- which is the whole defect this commit removes.
    #[cfg(unix)]
    #[test]
    fn a_parser_stuck_after_eof_is_refused_as_this_crates_bug_not_as_containment() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "echo diagnostic"]);
        command.stdout(std::process::Stdio::piped());
        let mut child = command.spawn().expect("spawn closing fixture");
        let stdout = child.stdout.take().expect("fixture stdout pipe");

        // The parser blocks after EOF until this test releases it. Nothing but
        // the bound can end the wait, and nothing is left running once it does.
        let (release, held) = std::sync::mpsc::channel::<()>();
        let channel = super::spawn_pipe_parser(
            stdout,
            std::sync::Arc::new(super::CompilerProgress::new()),
            move |mut reader| {
                let mut drained = String::new();
                std::io::Read::read_to_string(&mut reader, &mut drained)
                    .map_err(|error| error.to_string())?;
                let _ = held.recv();
                Ok(drained)
            },
        );

        let _ = child.wait().expect("reap closing fixture");
        let liveness_bound = std::time::Duration::from_millis(400);
        let started = std::time::Instant::now();
        let error = super::receive_compiler_output_within(
            channel,
            "test cargo stdout",
            std::time::Duration::from_millis(200),
            liveness_bound,
        )
        .expect_err("a parser that never returns must not hang the run forever");
        assert!(
            started.elapsed() >= liveness_bound,
            "the refusal must come from the liveness bound, not the close bound: {:?}",
            started.elapsed()
        );
        assert!(
            error.contains("liveness bug in this crate's own parser"),
            "the refusal must name itself as this crate's bug: {error}"
        );
        assert!(
            error.contains("The pipe is CLOSED"),
            "the refusal must record that containment was already discharged: {error}"
        );
        assert!(
            !error.contains("uncontained"),
            "a shut pipe may never be reported as a containment finding: {error}"
        );
        let _ = release.send(());
    }

    /// A write end a surviving process still holds is the containment failure
    /// the bound is for. It must still fire -- and it must say who.
    ///
    /// The holder is a direct child of THIS process because that is the shape
    /// that is actually diagnosable by pid and argv. The one long-lived child a
    /// run starts on purpose, `trustd`, is excluded from the walk so no kill can
    /// reach it, and a holder that was reparented onto init is unreachable from
    /// any pid walk; the message says both rather than hiding them.
    #[cfg(all(unix, any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn a_write_end_a_surviving_child_still_holds_fails_and_names_the_holder() {
        use std::os::fd::FromRawFd as _;

        struct Holder(std::process::Child);
        impl Drop for Holder {
            fn drop(&mut self) {
                // Started by this test, so this test cleans it up.
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }

        let mut fds = [0 as libc::c_int; 2];
        // SAFETY: `fds` is a 2-element array, which is what `pipe` writes.
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0, "create the evidence pipe");
        for fd in fds {
            // Close-on-exec on THIS process's copies, so a child spawned by
            // some other test running in parallel cannot become an accidental
            // second holder. `Stdio::from(File)` dup2s into the child, which
            // clears the flag there -- that inheritance is the thing modelled.
            // SAFETY: `fd` is one of the two descriptors just created.
            assert_eq!(unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) }, 0, "cloexec");
        }
        // SAFETY: both descriptors come from the `pipe` above and are moved
        // into owning `File`s exactly once.
        let read_end = unsafe { std::fs::File::from_raw_fd(fds[0]) };
        let write_end = unsafe { std::fs::File::from_raw_fd(fds[1]) };

        let holder = Holder(
            std::process::Command::new("/bin/sh")
                .args(["-c", "exec sleep 30"])
                .stdin(std::process::Stdio::null())
                .stdout(write_end.try_clone().expect("holder write end"))
                .stderr(std::process::Stdio::null())
                .spawn()
                .expect("spawn the surviving holder"),
        );
        let holder_pid = holder.0.id();

        let mut leader = std::process::Command::new("/bin/sh")
            .args(["-c", "echo diagnostic"])
            .stdin(std::process::Stdio::null())
            .stdout(write_end.try_clone().expect("leader write end"))
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn the leader");
        // Every write end except the holder's is now closed: the leader is
        // reaped, and this process drops its own copy.
        let _ = leader.wait().expect("reap the leader");
        drop(write_end);

        let close_bound = std::time::Duration::from_millis(400);
        let channel = super::spawn_pipe_parser(
            read_end,
            std::sync::Arc::new(super::CompilerProgress::new()),
            |mut reader| {
                let mut drained = Vec::new();
                std::io::Read::read_to_end(&mut reader, &mut drained)
                    .map_err(|error| error.to_string())?;
                Ok(drained.len())
            },
        );

        let started = std::time::Instant::now();
        let error = super::receive_compiler_output_within(
            channel,
            "test cargo stdout",
            close_bound,
            super::POST_EOF_PARSE_LIVENESS_BOUND,
        )
        .expect_err("a held write end is exactly what this bound is for");
        assert!(
            started.elapsed() >= close_bound,
            "the bound must be spent before refusing: {:?}",
            started.elapsed()
        );
        assert!(error.contains("did not reach end-of-file"), "{error}");
        assert!(
            error.contains("blocked inside read(2)"),
            "the refusal must say what it measured: {error}"
        );
        assert!(
            error.contains(&format!("pid {holder_pid}")),
            "the refusal must name the holder (pid {holder_pid}): {error}"
        );
        assert!(error.contains("sleep"), "the refusal must carry the holder's argv: {error}");
        assert!(
            error.contains("`trustd` is never a member of this walk"),
            "a list that omits the daemon must say so: {error}"
        );
        drop(holder);
    }

    /// The reverse of the pair: a parser that gives up BEFORE end-of-file still
    /// has its result delivered, rather than being re-diagnosed as a pipe that
    /// never closed. This is how a malformed-transport refusal reaches its
    /// caller while some descendant is still holding the stream open.
    #[cfg(unix)]
    #[test]
    fn a_parser_that_returns_before_eof_is_still_delivered() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "echo diagnostic; exec sleep 30"]);
        command.stdout(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let mut child = command.spawn().expect("spawn never-closing fixture");
        let stdout = child.stdout.take().expect("fixture stdout pipe");

        let channel: super::CompilerOutputChannel<String> = super::spawn_pipe_parser(
            stdout,
            std::sync::Arc::new(super::CompilerProgress::new()),
            |reader| {
                let mut first = String::new();
                std::io::BufRead::read_line(&mut std::io::BufReader::new(reader), &mut first)
                    .map_err(|error| error.to_string())?;
                Err(format!("refused after {}", first.trim()))
            },
        );

        let error = super::receive_compiler_output_within(
            channel,
            "test cargo stdout",
            std::time::Duration::from_millis(400),
            super::POST_EOF_PARSE_LIVENESS_BOUND,
        )
        .expect_err("the parser refused");
        assert_eq!(error, "refused after diagnostic");
        let _ = crate::process_lifecycle::stop_tree(
            child.id(),
            crate::process_lifecycle::StopCause::Error,
        );
        let _ = child.kill();
        let _ = child.wait();
    }

    /// `process_argv` is the half of the diagnostic that makes a named pid
    /// actionable, so it is asserted against a process whose argv this test
    /// chose.
    #[cfg(all(unix, any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn a_named_process_carries_its_argv() {
        let mut child = std::process::Command::new("/bin/sh")
            .args(["-c", "exec sleep 30"])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn argv fixture");
        let argv = super::process_argv(child.id());
        let _ = child.kill();
        let _ = child.wait();
        let argv = argv.expect("this platform reports argv");
        assert!(argv.contains("sleep"), "{argv}");
        assert!(argv.len() <= super::MAX_RENDERED_ARGV_BYTES + 3, "{argv}");
    }

    /// An empty descendant list is a finding, not an omission: it says the
    /// holder is not reachable from this process and names the tool that can
    /// find it. The old message asserted a cause instead.
    #[test]
    fn an_unreachable_holder_is_reported_as_unreachable() {
        let rendered = super::render_surviving_descendants(&super::SurvivingDescendants::Walked {
            members: Vec::new(),
            truncated: false,
        });
        assert!(rendered.contains("no process still descends from this one"), "{rendered}");
        assert!(rendered.contains("lsof"), "{rendered}");
        assert!(!rendered.contains("may still own"), "{rendered}");
        // The walk skips `trustd` by construction; an empty list must not read
        // as having cleared it.
        assert!(rendered.contains("`trustd` is never a member of this walk"), "{rendered}");

        // "The walk failed" and "the walk found nobody" are different claims.
        let unavailable =
            super::render_surviving_descendants(&super::SurvivingDescendants::Unavailable);
        assert!(unavailable.contains("no process-tree walk"), "{unavailable}");
        assert!(!unavailable.contains("no process still descends"), "{unavailable}");
    }

    #[test]
    fn timeout_messages_name_the_bound_and_size_up_the_clocks() {
        // `{:?}` renders the shipped ceiling as `28800s` and an elapsed as
        // `7231.418902341s`. An operator reading a killed build needs to size
        // these up at a glance, so they are rendered in whole units.
        assert_eq!(
            super::format_bound_duration(super::COMPILER_PROCESS_REFERENCE_CEILING),
            "8h00m00s"
        );
        assert_eq!(super::format_bound_duration(super::COMPILER_PROGRESS_IDLE_TIMEOUT), "30m00s");
        assert_eq!(
            super::format_bound_duration(std::time::Duration::from_micros(7_231_418_902)),
            "2h00m31s"
        );
        assert_eq!(super::format_bound_duration(std::time::Duration::from_millis(700)), "700ms");

        let detail = |bound| super::CompilerTimeoutDetail {
            bound,
            limit: super::COMPILER_PROGRESS_IDLE_TIMEOUT,
            elapsed: std::time::Duration::from_secs(4512),
            idle: std::time::Duration::from_secs(901),
            idle_limit: super::COMPILER_PROGRESS_IDLE_TIMEOUT,
            cpu: super::CompilerCpuEvidence::Unsampled,
        };
        let idle = detail(super::CompilerTimeoutBound::Idle).message();
        assert!(idle.contains("stopped making progress"), "{idle}");
        assert!(idle.contains("15m01s"), "{idle}");
        assert!(idle.contains("30m00s idle bound"), "{idle}");
        assert!(idle.contains("running 1h15m12s"), "{idle}");
        // Without a reading the message must SAY there was no reading rather
        // than assert something about CPU it cannot know.
        assert!(idle.contains("CPU time could not be sampled"), "{idle}");

        // With one, the idle message has to carry both halves of the verdict
        // and both numbers: an operator reading a killed build needs to see
        // that the process was neither talking nor computing.
        let idle_with_cpu = super::CompilerTimeoutDetail {
            cpu: super::CompilerCpuEvidence::Sampled {
                consumed: std::time::Duration::from_secs(3600),
                since_advance: std::time::Duration::from_secs(1802),
            },
            ..detail(super::CompilerTimeoutBound::Idle)
        }
        .message();
        assert!(idle_with_cpu.contains("stopped making progress"), "{idle_with_cpu}");
        assert!(idle_with_cpu.contains("stdout/stderr for 15m01s"), "{idle_with_cpu}");
        assert!(idle_with_cpu.contains("consumed no CPU for 30m02s"), "{idle_with_cpu}");
        assert!(idle_with_cpu.contains("having consumed 1h00m00s of CPU"), "{idle_with_cpu}");
        assert!(idle_with_cpu.contains("30m00s idle bound"), "{idle_with_cpu}");

        // The absolute message's old claim -- "it kept producing output" -- is
        // no longer the only way to outrun the idle bound, so it may not be
        // stated as though it were.
        let absolute_with_cpu = super::CompilerTimeoutDetail {
            limit: super::COMPILER_PROCESS_REFERENCE_CEILING,
            cpu: super::CompilerCpuEvidence::Sampled {
                consumed: std::time::Duration::from_secs(25000),
                since_advance: std::time::Duration::from_secs(12),
            },
            ..detail(super::CompilerTimeoutBound::Absolute)
        }
        .message();
        assert!(absolute_with_cpu.contains("6h56m40s of CPU consumed"), "{absolute_with_cpu}");
        assert!(absolute_with_cpu.contains("last CPU advance 12s ago"), "{absolute_with_cpu}");
        assert!(absolute_with_cpu.contains("output or CPU"), "{absolute_with_cpu}");
        assert!(absolute_with_cpu.contains("30m00s idle bound never fired"), "{absolute_with_cpu}");

        let absolute = super::CompilerTimeoutDetail {
            limit: super::COMPILER_PROCESS_REFERENCE_CEILING,
            ..detail(super::CompilerTimeoutBound::Absolute)
        }
        .message();
        assert!(absolute.contains("exceeded the 8h00m00s absolute bound"), "{absolute}");
        assert!(absolute.contains("30m00s idle bound never fired"), "{absolute}");

        let silent = super::CompilerTimeoutDetail {
            limit: super::COMPILER_SILENT_PROCESS_TIMEOUT,
            ..detail(super::CompilerTimeoutBound::Silent)
        }
        .message();
        assert!(
            silent.contains("no output at all within the 2h00m00s silent-process bound"),
            "{silent}"
        );
        assert!(silent.contains("idle bound never armed"), "{silent}");
    }

    #[test]
    fn the_backstop_scales_every_compiler_process_bound() {
        use trust_types::determinism::Backstop;
        // The builtin backstop reproduces the shipped bounds exactly.
        assert_eq!(
            super::CompilerProcessBounds::from_backstop(Backstop::BUILTIN),
            super::CompilerProcessBounds::DEFAULT
        );
        // ay's retired 72,000 s ceiling is backstop 2,500, which also scales
        // the stall bounds: one knob, one factor.
        let ay = super::CompilerProcessBounds::from_backstop(Backstop { per_mille: 2500 });
        assert_eq!(ay.absolute, std::time::Duration::from_secs(72_000));
        assert_eq!(ay.idle, std::time::Duration::from_secs(75 * 60));
        assert_eq!(ay.silent, std::time::Duration::from_secs(5 * 60 * 60));
        // Below 1000 the process bounds stay at the reference: the negative
        // control (`backstop = 1`) shortens the solver clocks only, so the
        // build it judges still reaches a report (T7b-BACKSTOP-1).
        for per_mille in [1, 25, 999] {
            assert_eq!(
                super::CompilerProcessBounds::from_backstop(Backstop { per_mille }),
                super::CompilerProcessBounds::DEFAULT,
                "{per_mille}"
            );
        }
        for bounds in [ay, super::CompilerProcessBounds::DEFAULT] {
            assert!(bounds.idle <= bounds.silent && bounds.silent <= bounds.absolute, "{bounds:?}");
        }
        // The largest multiplier saturates rather than wrapping.
        let largest = super::CompilerProcessBounds::from_backstop(Backstop { per_mille: u32::MAX });
        assert!(largest.absolute > super::COMPILER_PROCESS_REFERENCE_CEILING, "{largest:?}");
    }

    /// T7b: a process the backstop ended could not run, so it exits 3.
    #[test]
    fn a_compiler_the_backstop_ended_could_not_run() {
        use trust_types::determinism::Backstop;
        for per_mille in [1, 1000, 2500] {
            assert_eq!(
                super::backstop_ended_the_compiler(
                    "the silent-process bound fired",
                    Backstop { per_mille }
                ),
                std::process::ExitCode::from(crate::determinism_report::EXIT_COULD_NOT_RUN),
            );
        }
    }

    /// Spawn a `/bin/sh` compiler stand-in whose stderr is drained exactly the
    /// way a real verified compile's is, and run it under `bounds`.
    #[cfg(unix)]
    fn run_drained_fixture(
        script: &str,
        bounds: super::CompilerProcessBounds,
    ) -> (Result<(), String>, std::time::Duration) {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", script]);
        command.stderr(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let started = std::time::Instant::now();
        let mut child = command.spawn().expect("spawn compiler fixture");
        let stderr = child.stderr.take().expect("compiler stderr pipe");
        let mut guard = super::CompilerProcessGuard::start(child.id(), bounds);
        let output = super::spawn_compiler_stderr_parser(
            stderr,
            guard.progress(),
            true,
            false,
            false,
            String::new(),
            false,
        );
        let _ = super::wait_for_compiler_process(&mut child, &mut guard).expect("wait compiler");
        let outcome = guard.finish();
        let elapsed = started.elapsed();
        super::receive_compiler_output(output, "test compiler stderr")
            .expect("compiler must close stderr");
        (outcome, elapsed)
    }

    #[cfg(unix)]
    #[test]
    fn compiler_that_keeps_emitting_outlives_the_idle_bound() {
        // ~3s of work in 100ms diagnostic steps under a 1s idle bound: the old
        // flat cap would have killed this at 1s even though it never stalled.
        //
        // Every bound this fixture could die on is shorter than its own
        // lifetime, so surviving is only possible by recording progress: with
        // the drains' progress signal removed the silent bound kills it at 1s.
        let (outcome, elapsed) = run_drained_fixture(
            "i=0; while [ $i -lt 30 ]; do echo diagnostic >&2; sleep 0.1; i=$((i+1)); done",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_secs(1),
                idle: std::time::Duration::from_secs(1),
                absolute: std::time::Duration::from_secs(60),
            },
        );
        outcome.expect("a compiler making steady progress must not be killed");
        assert!(elapsed > std::time::Duration::from_secs(2), "fixture ended early: {elapsed:?}");
    }

    #[cfg(unix)]
    #[test]
    fn compiler_that_goes_quiet_dies_at_the_idle_bound() {
        // Emits once, then stalls with a live background descendant. The idle
        // bound must fire (not the silent one) and take the whole group.
        let (outcome, elapsed) = run_drained_fixture(
            "echo diagnostic >&2; sleep 30 & wait",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_secs(30),
                idle: std::time::Duration::from_millis(700),
                absolute: std::time::Duration::from_secs(30),
            },
        );
        let error = outcome.expect_err("a stalled compiler must be killed");
        assert!(error.contains("stopped making progress"), "{error}");
        assert!(error.contains("idle bound"), "{error}");
        assert!(elapsed < std::time::Duration::from_secs(10), "idle bound was not enforced");
    }

    #[cfg(unix)]
    #[test]
    fn compiler_that_streams_forever_dies_at_the_absolute_bound() {
        // Never idle, never finished: only the absolute ceiling can stop it.
        //
        // The silent bound is set *below* the absolute one so it cannot be
        // what supplies the kill: without recorded progress this dies at 400ms
        // with the silent message, and both assertions below reject that.
        let (outcome, elapsed) = run_drained_fixture(
            "while :; do echo diagnostic >&2; sleep 0.02; done",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_millis(400),
                idle: std::time::Duration::from_secs(10),
                absolute: std::time::Duration::from_millis(800),
            },
        );
        let error = outcome.expect_err("an endlessly streaming compiler must be killed");
        assert!(error.contains("absolute bound"), "{error}");
        assert!(
            elapsed >= std::time::Duration::from_millis(700),
            "a streaming compiler must outlive the silent bound: {elapsed:?}"
        );
        assert!(elapsed < std::time::Duration::from_secs(10), "absolute bound was not enforced");
    }

    #[cfg(unix)]
    #[test]
    fn compiler_that_produces_nothing_still_dies_at_the_silent_bound() {
        // The no-output case is unchanged: neither the (shorter) idle bound
        // nor the (longer) absolute bound may move a silent process's death.
        let (outcome, elapsed) = run_drained_fixture(
            "sleep 30",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_millis(400),
                idle: std::time::Duration::from_millis(50),
                absolute: std::time::Duration::from_secs(30),
            },
        );
        let error = outcome.expect_err("a silent compiler must be killed");
        assert!(error.contains("silent-process bound"), "{error}");
        assert!(error.contains("idle bound never armed"), "{error}");
        assert!(
            elapsed >= std::time::Duration::from_millis(350),
            "the idle bound must not shorten a silent process: {elapsed:?}"
        );
        assert!(elapsed < std::time::Duration::from_secs(10), "silent bound was not enforced");
    }

    /// A `/bin/sh` fixture that reaps itself and its whole process group when
    /// it goes out of scope -- INCLUDING when the test unwinds on a failed
    /// assertion. The spinning variant below pins a core, so a fixture that
    /// only cleaned up on the success path would leave one running for as long
    /// as the machine stayed up every time the test failed.
    #[cfg(unix)]
    struct GroupFixture(std::process::Child);

    #[cfg(unix)]
    impl GroupFixture {
        /// `own_group` mirrors `CompilerProcessGuard::configure`; passing
        /// `false` produces a child that inherits the harness's group, which
        /// the sampler must refuse.
        fn spawn(script: &str, own_group: bool) -> Self {
            let mut command = std::process::Command::new("/bin/sh");
            command.args(["-c", script]);
            command.stderr(std::process::Stdio::null());
            if own_group {
                super::CompilerProcessGuard::configure(&mut command);
            }
            Self(command.spawn().expect("spawn group fixture"))
        }

        fn pid(&self) -> u32 {
            self.0.id()
        }
    }

    #[cfg(unix)]
    impl Drop for GroupFixture {
        fn drop(&mut self) {
            // The group kill first: the leader only waits, so killing it alone
            // would orphan the spinner it is waiting on.
            let _ = crate::process_lifecycle::stop_tree(
                self.0.id(),
                crate::process_lifecycle::StopCause::Error,
            );
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }

    /// What [`SelfTimedTree`]'s burner does with the CPU it is given.
    #[cfg(unix)]
    #[derive(Clone, Copy)]
    enum Burner {
        /// Spin for ever, storing its own reading after every `getrusage`.
        Spins,
        /// Spin until its own clock reads this much, then sleep, waking only
        /// to store its reading when [`SelfTimedTree::own_cpu`] asks.
        SleepsAfter(std::time::Duration),
    }

    /// A process tree this test builds with `fork` alone, whose one busy
    /// member says how much CPU it has used by a clock the sampler under test
    /// never reads: its own `getrusage(RUSAGE_SELF)`. That is the kernel's
    /// account of the same CPU, reached without the per-pid query and without
    /// the unit conversion `CpuClock::read` applies, so a sampler whose
    /// conversion is off by the Mach timebase (41.7x here: the defect
    /// `CpuClock::read` records) disagrees with it by exactly that, on an idle
    /// host and on a loaded one alike. A `/bin/sh` fixture has no such clock.
    ///
    /// The root leads a process group of its own, as
    /// `CompilerProcessGuard::configure` makes a compiler's, and only waits
    /// (`pause`). Its one child, the burner, stays in the root's group and
    /// stores its own reading in a page it shares with this process: after
    /// every `getrusage` while it spins, and, once it sleeps, each time this
    /// process asks for one (a byte on a pipe), so that a sleeping burner's own
    /// account is read at the same moments as the sampler's.
    ///
    /// Nothing is exec'd, so both forked processes make only system calls
    /// (`setpgid`, `open`, `dup2`, `close`, `fork`, `getpid`, `getrusage`,
    /// `read`, `pause`, `_exit`) and atomic stores: nothing allocates, and
    /// nothing takes a lock another thread of this process may have held at
    /// the fork. Their stdio is `/dev/null` and they close descriptors 3 to
    /// 1023, as `hold_no_other_descriptor` does in the lifecycle tests and for
    /// its reason: the harness runs tests in parallel.
    #[cfg(unix)]
    struct SelfTimedTree {
        root: libc::pid_t,
        /// The shared page, as words: [`Self::OWN`], [`Self::ANSWERS`],
        /// [`Self::BURNER`].
        shared: *mut std::sync::atomic::AtomicU64,
        /// This process's end of a sleeping burner's wake pipe; -1 otherwise.
        wake: libc::c_int,
        /// How many readings this process has asked a sleeping burner for.
        asked: std::cell::Cell<u64>,
    }

    #[cfg(unix)]
    impl SelfTimedTree {
        /// The burner's last own reading in nanoseconds, plus one (0: none yet).
        const OWN: usize = 0;
        /// How many readings a sleeping burner has stored on being asked.
        const ANSWERS: usize = 1;
        /// The burner's pid (0: not yet known).
        const BURNER: usize = 2;
        const PAGE: usize = 4096;

        fn spawn(burner: Burner) -> Self {
            // SAFETY: a fresh anonymous shared mapping, checked before use. It
            // is zero-filled, so every word starts at 0.
            let page = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    Self::PAGE,
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_SHARED | libc::MAP_ANON,
                    -1,
                    0,
                )
            };
            assert_ne!(
                page,
                libc::MAP_FAILED,
                "map the self-timed fixture's page: {}",
                std::io::Error::last_os_error()
            );
            let shared = page.cast::<std::sync::atomic::AtomicU64>();
            let sleep_after = match burner {
                Burner::Spins => None,
                Burner::SleepsAfter(burn) => {
                    Some(u64::try_from(burn.as_nanos()).unwrap_or(u64::MAX))
                }
            };
            let mut pipe: [libc::c_int; 2] = [-1, -1];
            if sleep_after.is_some() {
                // SAFETY: `pipe` is the two-element array `pipe` writes.
                let created = unsafe { libc::pipe(pipe.as_mut_ptr()) };
                assert_eq!(created, 0, "the wake pipe: {}", std::io::Error::last_os_error());
                for fd in pipe {
                    // SAFETY: both descriptors were just created here.
                    unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
                }
            }
            // SAFETY: the forked side runs `self_timed_root`, which makes only
            // system calls and never returns (type docs).
            let root = unsafe { libc::fork() };
            if root == 0 {
                unsafe { self_timed_root(shared, pipe[0], sleep_after) }
            }
            let forked = std::io::Error::last_os_error();
            // SAFETY: descriptors and the mapping created above, closed once.
            unsafe {
                if pipe[0] >= 0 {
                    libc::close(pipe[0]);
                }
                if root < 0 {
                    if pipe[1] >= 0 {
                        libc::close(pipe[1]);
                    }
                    libc::munmap(page, Self::PAGE);
                }
            }
            assert!(root > 0, "fork the self-timed fixture: {forked}");
            // The root sets its group itself too: whichever call comes first,
            // it leads its own group before this returns, so no sample taken
            // from here on can find it otherwise.
            // SAFETY: our own child, which has not exec'd.
            unsafe { libc::setpgid(root, root) };
            Self { root, shared, wake: pipe[1], asked: std::cell::Cell::new(0) }
        }

        fn word(&self, index: usize) -> &std::sync::atomic::AtomicU64 {
            // SAFETY: `index` names one of the three words of the page, which
            // stays mapped for as long as `self` lives.
            unsafe { &*self.shared.add(index) }
        }

        fn pid(&self) -> u32 {
            u32::try_from(self.root).expect("a forked pid is positive")
        }

        /// The burner's pid, once it has stored it.
        fn burner(&self) -> Option<u32> {
            let pid = self.word(Self::BURNER).load(std::sync::atomic::Ordering::Acquire);
            u32::try_from(pid).ok().filter(|&pid| pid != 0)
        }

        /// The burner's last own reading as stored, without asking for one.
        fn last_own(&self) -> Option<std::time::Duration> {
            let biased = self.word(Self::OWN).load(std::sync::atomic::Ordering::Acquire);
            biased.checked_sub(1).map(std::time::Duration::from_nanos)
        }

        /// The burner's own reading of its CPU, current: a spinner's last is
        /// at most one loop old, and a sleeper is woken to store one, which
        /// this waits for (up to `within`; `None` if it never comes).
        fn own_cpu(&self, within: std::time::Duration) -> Option<std::time::Duration> {
            if self.wake >= 0 {
                let byte = 0_u8;
                // SAFETY: one byte from a local, to this fixture's own pipe.
                if unsafe { libc::write(self.wake, (&raw const byte).cast(), 1) } != 1 {
                    return None;
                }
                self.asked.set(self.asked.get() + 1);
                let deadline = std::time::Instant::now() + within;
                while self.word(Self::ANSWERS).load(std::sync::atomic::Ordering::Acquire)
                    < self.asked.get()
                {
                    if std::time::Instant::now() >= deadline {
                        return None;
                    }
                    std::thread::sleep(std::time::Duration::from_micros(100));
                }
            }
            self.last_own()
        }

        /// One sample of this tree by a fresh sampler, between two of the
        /// burner's own readings: what the burner had really used when the
        /// sampler read it lies between `before` and `after`.
        fn read(&self, within: std::time::Duration) -> SelfTimedReading {
            let before = self.own_cpu(within);
            let mut sampler = super::ProcessTreeCpuSampler::new();
            let sample = sampler.sample(self.pid()).then(|| sampler.reading().to_vec());
            let after = self.own_cpu(within);
            SelfTimedReading { before, sample, after }
        }
    }

    #[cfg(unix)]
    impl Drop for SelfTimedTree {
        fn drop(&mut self) {
            // The root leads its own group and nothing in the tree leaves it,
            // so one group SIGKILL ends both, whatever dispositions they
            // inherited; then the root is reaped (the burner, orphaned, by
            // init).
            // SAFETY: the root is this fixture's unreaped child, so its pid
            // and group id name nothing else; the pipe end and the page are
            // this fixture's own, released once.
            unsafe {
                libc::killpg(self.root, libc::SIGKILL);
                let mut status = 0;
                libc::waitpid(self.root, &raw mut status, 0);
                if self.wake >= 0 {
                    libc::close(self.wake);
                }
                libc::munmap(self.shared.cast(), Self::PAGE);
            }
        }
    }

    /// See [`SelfTimedTree::read`].
    #[cfg(unix)]
    struct SelfTimedReading {
        before: Option<std::time::Duration>,
        sample: Option<Vec<(u32, u64)>>,
        after: Option<std::time::Duration>,
    }

    /// This process's own CPU, user plus system, in nanoseconds, by
    /// `getrusage(RUSAGE_SELF)`: one system call, which a forked child of a
    /// multi-threaded process may make.
    #[cfg(unix)]
    fn own_cpu_nanos() -> u64 {
        let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
        // SAFETY: `usage` is a valid out-parameter for `getrusage`.
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) } != 0 {
            return 0;
        }
        // SAFETY: `getrusage` succeeded, so it wrote the whole struct.
        let usage = unsafe { usage.assume_init() };
        let micros = |time: libc::timeval| {
            u64::try_from(time.tv_sec)
                .unwrap_or(0)
                .saturating_mul(1_000_000)
                .saturating_add(u64::try_from(time.tv_usec).unwrap_or(0))
        };
        micros(usage.ru_utime).saturating_add(micros(usage.ru_stime)).saturating_mul(1_000)
    }

    /// The forked root of a [`SelfTimedTree`]: it leads its own group, keeps
    /// no descriptor above stdio but `wake` (which only its burner keeps),
    /// forks the burner, and waits for ever. System calls only.
    #[cfg(unix)]
    unsafe fn self_timed_root(
        shared: *mut std::sync::atomic::AtomicU64,
        wake: libc::c_int,
        sleep_after: Option<u64>,
    ) -> ! {
        // SAFETY: system calls on this process's own descriptors.
        unsafe {
            libc::setpgid(0, 0);
            let null = libc::open(c"/dev/null".as_ptr(), libc::O_RDWR);
            if null >= 0 {
                for fd in 0..3 {
                    libc::dup2(null, fd);
                }
            }
            for fd in 3..1024 {
                if fd != wake {
                    libc::close(fd);
                }
            }
            match libc::fork() {
                0 => self_timed_burner(shared, wake, sleep_after),
                -1 => libc::_exit(127),
                _ => {
                    if wake >= 0 {
                        libc::close(wake);
                    }
                    loop {
                        libc::pause();
                    }
                }
            }
        }
    }

    /// The burner of a [`SelfTimedTree`]. System calls and atomic stores only.
    #[cfg(unix)]
    unsafe fn self_timed_burner(
        shared: *mut std::sync::atomic::AtomicU64,
        wake: libc::c_int,
        sleep_after: Option<u64>,
    ) -> ! {
        use std::sync::atomic::Ordering;
        // SAFETY: the three words of the shared page, mapped in this process
        // too; system calls only.
        unsafe {
            let own = &*shared.add(SelfTimedTree::OWN);
            let answers = &*shared.add(SelfTimedTree::ANSWERS);
            (*shared.add(SelfTimedTree::BURNER))
                .store(u64::try_from(libc::getpid()).unwrap_or(0), Ordering::Release);
            loop {
                let used = own_cpu_nanos();
                own.store(used.saturating_add(1), Ordering::Release);
                if sleep_after.is_some_and(|after| used >= after) {
                    break;
                }
            }
            // Asleep: one reading per byte asked for, until end of file.
            let mut byte = 0_u8;
            while libc::read(wake, (&raw mut byte).cast(), 1) == 1 {
                own.store(own_cpu_nanos().saturating_add(1), Ordering::Release);
                answers.fetch_add(1, Ordering::AcqRel);
            }
            loop {
                libc::pause();
            }
        }
    }

    /// The coarser grain of the two clocks the spinning-tree test compares:
    /// `getrusage` counts microseconds, and `CpuClock` reads Mach time on
    /// macOS but whole clock ticks (`_SC_CLK_TCK`, 10ms) on Linux.
    #[cfg(unix)]
    fn cpu_clock_grain() -> std::time::Duration {
        #[cfg(target_os = "linux")]
        {
            // SAFETY: `sysconf` has no preconditions.
            let ticks = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
            if let Ok(ticks) = u64::try_from(ticks) {
                if ticks > 0 {
                    return std::time::Duration::from_nanos(1_000_000_000 / ticks);
                }
            }
        }
        // Measured 2026-10-14 here: the sampler read at most 18us past the
        // descendants' own readings around it (360 readings, load 22-56).
        std::time::Duration::from_micros(100)
    }

    /// The sampler under the guard, on its own: it must read a spinning
    /// DESCENDANT's CPU as that process counts it itself (the root here only
    /// waits, which is exactly the shape of a cargo leader draining its
    /// in-flight rustc jobs), must not read CPU a sleeping descendant did not
    /// use, must refuse a pid that does not lead its own group, and must be
    /// cheap enough that the interval below is not the binding cost.
    ///
    /// The descendants here share their root's group, so this case is one a
    /// group walk also passes -- which is why it did not catch the defect.
    /// `cpu_sample_follows_the_tree_out_of_the_drivers_process_group` below is
    /// the case that separates them.
    ///
    /// Every reading is checked against what the descendants count by their
    /// own clocks ([`SelfTimedTree`]), and every wait is armed on those
    /// clocks, never on how long a fixture was given: beside a load generator
    /// at load 43 a fixed 400ms gave a spinner 8-33ms of CPU in 30 runs of 30
    /// (measured 2026-10-13). Arming on the SAMPLER's reading instead, as
    /// db181d4e78 did, made "it spun `SPUN`" true by construction: a sampler
    /// that read 41.7x too little passed by waiting 41.7x longer (5 of 5,
    /// 2026-10-14). So the rate is checked again, as agreement: the sampler
    /// must read what the descendant's own clock counts, within a factor of
    /// `AGREE`, at each reading and over the window between them, which is
    /// `WINDOW` of the spinner's own CPU. Load stretches that window in wall
    /// time and changes neither side of the comparison.
    #[cfg(unix)]
    #[test]
    fn process_tree_cpu_sample_separates_a_spinning_tree_from_a_sleeping_one() {
        /// What the spinning tree must be seen to burn between the readings,
        /// and what each descendant burns by its own clock before the first.
        const SPUN: std::time::Duration = std::time::Duration::from_millis(40);
        /// The window between the readings, by the spinner's own clock: the
        /// 400ms of a pinned core this test once waited for in wall time.
        const WINDOW: std::time::Duration = std::time::Duration::from_millis(400);
        /// How far the sampler may stray from a descendant's own clock, as a
        /// factor either way (plus the clocks' grain, `cpu_clock_grain`).
        /// Measured 2026-10-14, 90 runs at load 22-56 (30 of them beside a
        /// load generator): the two agreed within 0.6% over the window and
        /// within 18us at every reading. Two is far wider than that, with room
        /// for hosts not measured here; a Mach-timebase error, 41.7x, is
        /// twenty times outside it.
        const AGREE: u32 = 2;
        /// A hang detector, not a latency budget: unloaded, the waits below
        /// end in about `SPUN` and then `WINDOW`, on the state they wait for.
        const HANG: std::time::Duration = std::time::Duration::from_secs(60);
        const POLL: std::time::Duration = std::time::Duration::from_millis(5);

        // Every reading is taken into a local and every assertion is made
        // after the last one, so no failure path can escape the fixtures'
        // `Drop`.
        let spinner = SelfTimedTree::spawn(Burner::Spins);
        let sleeper = SelfTimedTree::spawn(Burner::SleepsAfter(SPUN));
        // Not group-leading: the sampler must read nothing rather than read
        // this test process's own group and call it the child's liveness.
        let inherited = GroupFixture::spawn("sleep 300", false);

        let burned = |tree: &SelfTimedTree| {
            tree.burner().is_some() && tree.last_own().is_some_and(|own| own >= SPUN)
        };
        let armed = std::time::Instant::now();
        let started = loop {
            let started = burned(&spinner) && burned(&sleeper);
            if started || armed.elapsed() >= HANG {
                break started;
            }
            std::thread::sleep(POLL);
        };
        let spin_first = spinner.read(HANG);
        let sleep_first = sleeper.read(HANG);

        let timed = std::time::Instant::now();
        let _ = live_tree_cpu_sum(spinner.pid());
        let one_sample = timed.elapsed();

        let enough = spin_first.after.map(|after| after + WINDOW);
        let window = std::time::Instant::now();
        while started
            && spinner.last_own().zip(enough).is_some_and(|(own, enough)| own < enough)
            && window.elapsed() < HANG
        {
            std::thread::sleep(POLL);
        }
        let window = window.elapsed();
        let spin_second = spinner.read(HANG);
        let sleep_second = sleeper.read(HANG);
        let inherited_reading = live_tree_cpu_sum(inherited.pid());

        assert!(
            started,
            "the descendants never counted {SPUN:?} of CPU by their own clocks within {HANG:?}: \
             the spinner counted {:?} (pid {:?}), the sleeper {:?} (pid {:?})",
            spinner.last_own(),
            spinner.burner(),
            sleeper.last_own(),
            sleeper.burner()
        );
        let grain = cpu_clock_grain();
        // `sampled` agrees with a descendant's own count, which lies between
        // `low` and `high`, within `AGREE` either way, give or take `grain`.
        let agrees =
            |sampled: std::time::Duration, low: std::time::Duration, high: std::time::Duration| {
                sampled * AGREE + grain >= low && sampled <= high * AGREE + grain
            };
        // What the sampler read for one descendant at one reading, between
        // what that descendant counted itself just before and just after.
        let seen = |reading: &SelfTimedReading, tree: &SelfTimedTree, what: &str| {
            let burner = tree.burner().expect("the descendant stored its pid first");
            let sampled = reading
                .sample
                .as_deref()
                .and_then(|sample| sample.iter().find(|&&(pid, _)| pid == burner))
                .map(|&(_, nanos)| std::time::Duration::from_nanos(nanos))
                .unwrap_or_else(|| {
                    panic!(
                        "the sampler did not read the {what} descendant (pid {burner}) of root {}: \
                         it read {:?}; a sampler that does not see descendants reads exactly this",
                        tree.pid(),
                        reading.sample
                    )
                });
            let own = |count: Option<std::time::Duration>| {
                count.unwrap_or_else(|| {
                    panic!(
                        "the {what} descendant (pid {burner}) never counted its CPU within {HANG:?}"
                    )
                })
            };
            (own(reading.before), sampled, own(reading.after))
        };
        let spin =
            [seen(&spin_first, &spinner, "spinning"), seen(&spin_second, &spinner, "spinning")];
        let sleep =
            [seen(&sleep_first, &sleeper, "sleeping"), seen(&sleep_second, &sleeper, "sleeping")];
        eprintln!(
            "the sampler against the descendants' own clocks (own before, sampled, own after): \
             spinning {spin:?}, sleeping {sleep:?}; window {window:?}"
        );
        for (what, [first, second]) in [("spinning", spin), ("sleeping", sleep)] {
            for (before, sampled, after) in [first, second] {
                assert!(
                    agrees(sampled, before, after),
                    "the sampler read {sampled:?} for the {what} descendant, which counted \
                     {before:?} just before and {after:?} just after by its own clock: they must \
                     agree within a factor of {AGREE}, give or take {grain:?}"
                );
            }
            let sampled = second.1.saturating_sub(first.1);
            let (low, high) = (second.0.saturating_sub(first.2), second.2.saturating_sub(first.0));
            assert!(
                agrees(sampled, low, high),
                "between the readings the sampler saw the {what} descendant use {sampled:?}, which \
                 counted {low:?} to {high:?} by its own clock over the same window ({window:?}): \
                 they must agree within a factor of {AGREE}, give or take {grain:?}"
            );
        }

        let total = |reading: &SelfTimedReading| {
            reading.sample.as_deref().map(|sample| {
                std::time::Duration::from_nanos(
                    sample.iter().fold(0_u64, |total, &(_, nanos)| total.saturating_add(nanos)),
                )
            })
        };
        let spun = total(&spin_second)
            .zip(total(&spin_first))
            .map(|(second, first)| second.saturating_sub(first))
            .expect("a spinning group must be sampleable twice");
        let slept = total(&sleep_second)
            .zip(total(&sleep_first))
            .map(|(second, first)| second.saturating_sub(first))
            .expect("a sleeping group must be sampleable twice");
        assert!(
            spun >= SPUN,
            "a spinning descendant must show consumed CPU, saw {spun:?} over {window:?}"
        );
        assert!(
            slept < super::COMPILER_CPU_ADVANCE_MIN,
            "a sleeping group must not clear the advance threshold, saw {slept:?} over {window:?}"
        );
        assert_eq!(
            inherited_reading, None,
            "a child that does not lead its own group must not be sampled"
        );
        eprintln!("one process-tree CPU sample took {one_sample:?}");
        assert!(
            one_sample < std::time::Duration::from_millis(5),
            "a CPU sample must be cheap enough to be unconditional, took {one_sample:?}"
        );
    }

    /// The naive sum over the members alive at THIS instant -- the reading the
    /// shipped sampler returned. It is kept only as a test helper: the
    /// production rule no longer works this way, and
    /// `cpu_accumulator_holds_the_work_of_a_member_that_exits` below is the
    /// measurement that says why it must not.
    #[cfg(unix)]
    fn live_tree_cpu_sum(root: u32) -> Option<std::time::Duration> {
        let mut sampler = super::ProcessTreeCpuSampler::new();
        if !sampler.sample(root) {
            return None;
        }
        Some(std::time::Duration::from_nanos(
            sampler.reading().iter().fold(0_u64, |total, &(_, nanos)| total.saturating_add(nanos)),
        ))
    }

    /// Read a pid a fixture has written for itself, waiting for it to appear.
    /// `None` means the descendant never started, which every caller treats as
    /// a broken fixture rather than as a result.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn fixture_pid(path: &std::path::Path, within: std::time::Duration) -> Option<u32> {
        let deadline = std::time::Instant::now() + within;
        loop {
            if let Ok(text) = std::fs::read_to_string(path) {
                if let Ok(pid) = text.trim().parse::<u32>() {
                    return Some(pid);
                }
            }
            if std::time::Instant::now() >= deadline {
                return None;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    /// A fixture shaped like cargo and its compilers: a leader that leads a
    /// process group of its own, plus a descendant that LEAVES that group at
    /// exec -- which is exactly what `cargo-util`'s `command.process_group(0)`
    /// does to every real compiler, and exactly what the group walk could not
    /// see.
    ///
    /// There is no `setpgid` built into `/bin/sh` and no `setsid` binary on
    /// macOS, so the isolated descendant is forked in the leader's `pre_exec`
    /// hook -- the one place this process can run code inside the leader after
    /// the fork and before it becomes `/bin/sh`. Everything the forked child
    /// does (`setpgid`, `execv`, `_exit`) is async-signal-safe, and its argv is
    /// built before the fork so nothing allocates on the wrong side of it.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct IsolatedDescendantFixture(std::process::Child);

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl IsolatedDescendantFixture {
        /// The descendant reports its own pid through `pid_path` before it does
        /// anything else. That is deliberately NOT recovered from
        /// `collect_process_tree`: the tests below have to be able to say "the
        /// fixture really did put a descendant outside the driver's group"
        /// while the walk under test is mutated to the group walk that cannot
        /// see it, or the mutation would fail them on their own premise
        /// instead of on their claim.
        fn spawn(leader_script: &str, descendant_script: &str, pid_path: &std::path::Path) -> Self {
            let descendant_script =
                format!("printf '%s' \"$$\" > '{}'; {descendant_script}", pid_path.display());
            Self::spawn_with_descendant(
                std::path::Path::new("/bin/sh"),
                &["sh", "-c", &descendant_script],
                &[],
                leader_script,
            )
        }

        /// As [`Self::spawn`], but the isolated descendant execs `program` with
        /// `argv` (argv[0] included) and the extra environment `envs`, so a
        /// test can give it the executable identity it needs. Reporting its
        /// pid is then the descendant's own business.
        fn spawn_with_descendant(
            program: &std::path::Path,
            argv: &[&str],
            envs: &[(&str, &std::ffi::OsStr)],
            leader_script: &str,
        ) -> Self {
            use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
            use std::os::unix::process::CommandExt as _;

            let program =
                std::ffi::CString::new(program.as_os_str().as_bytes()).expect("descendant path");
            let argv: Vec<std::ffi::CString> = argv
                .iter()
                .map(|arg| std::ffi::CString::new(*arg).expect("descendant argument"))
                .collect();
            // The argv pointer array is built HERE, before any fork: nothing may
            // allocate between `fork` and `execv` in a multi-threaded parent.
            // Raw pointers are not `Send`, so the array travels as addresses;
            // `argv` moves into the hook with it and keeps them valid.
            let mut pointers: Vec<usize> = argv.iter().map(|arg| arg.as_ptr() as usize).collect();
            pointers.push(0);
            // The descendant's environment is passed to `execve` explicitly:
            // `Command::envs` on the leader is NOT yet in effect inside its
            // `pre_exec` hook (measured: the descendant saw none of it). This
            // test process's own environment is inherited, `envs` on top.
            let mut environment: Vec<std::ffi::CString> = std::env::vars_os()
                .filter(|(key, _)| !envs.iter().any(|(name, _)| key.as_os_str() == *name))
                .chain(envs.iter().map(|(key, value)| ((*key).into(), (*value).to_os_string())))
                .filter_map(|(key, value)| {
                    let mut entry = key.into_vec();
                    entry.push(b'=');
                    entry.extend_from_slice(value.as_bytes());
                    std::ffi::CString::new(entry).ok()
                })
                .collect();
            environment.shrink_to_fit();
            let mut environment_pointers: Vec<usize> =
                environment.iter().map(|entry| entry.as_ptr() as usize).collect();
            environment_pointers.push(0);
            let mut command = std::process::Command::new("/bin/sh");
            command.args(["-c", leader_script]);
            command
                .stdin(std::process::Stdio::null())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null());
            super::CompilerProcessGuard::configure(&mut command);
            unsafe {
                command.pre_exec(move || {
                    let _keep_alive = (&argv, &environment);
                    let argv_pointers = pointers.as_ptr().cast::<*const libc::c_char>();
                    let environment_pointers =
                        environment_pointers.as_ptr().cast::<*const libc::c_char>();
                    match libc::fork() {
                        -1 => return Err(std::io::Error::last_os_error()),
                        0 => {
                            // The whole point of the fixture: a child of the
                            // leader that is NOT in the leader's group.
                            libc::setpgid(0, 0);
                            libc::execve(program.as_ptr(), argv_pointers, environment_pointers);
                            libc::_exit(127);
                        }
                        _ => {}
                    }
                    Ok(())
                });
            }
            Self(command.spawn().expect("spawn isolated-descendant fixture"))
        }

        fn pid(&self) -> u32 {
            self.0.id()
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl Drop for IsolatedDescendantFixture {
        fn drop(&mut self) {
            // The TREE kill, because the group kill is precisely what cannot
            // reach this fixture's descendant. Cleaning up with the group kill
            // would leave a spinning core behind on every failed assertion --
            // which is the defect these tests exist for, in miniature.
            let _ = crate::process_lifecycle::stop_tree(
                self.0.id(),
                crate::process_lifecycle::StopCause::Error,
            );
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }

    /// The defect this crate was sealed with. The sampler measured the driver's
    /// process GROUP; every compiler leaves that group at exec, so the measured
    /// set was the driver alone -- and the driver's CPU is spent draining child
    /// output, which is the OTHER liveness signal. The idle bound, which arms
    /// only while both are stale, was ANDing one clock with itself.
    ///
    /// This fixture is that shape at test speed: a leader that only sleeps, and
    /// one spinning descendant outside its group. Every nanosecond of CPU here
    /// is CPU a group walk cannot see, which is what the third assertion
    /// states directly rather than leaving to the mutation.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn cpu_sample_follows_the_tree_out_of_the_drivers_process_group() {
        let pid_path =
            std::env::temp_dir().join(format!("trust-tree-sample-spinner-{}", std::process::id()));
        let _ = std::fs::remove_file(&pid_path);
        let fixture =
            IsolatedDescendantFixture::spawn("sleep 30", "while :; do :; done", &pid_path);
        let spinner = fixture_pid(&pid_path, std::time::Duration::from_secs(5));
        let _ = std::fs::remove_file(&pid_path);
        // Let the descendant reach steady state before the first reading. Every
        // reading is captured before any assertion is made, so no failure path
        // can escape the fixture's `Drop`.
        std::thread::sleep(std::time::Duration::from_millis(250));

        let mut sampler = super::ProcessTreeCpuSampler::new();
        let first = sampler.sample(fixture.pid()).then(|| sampler.reading().to_vec());
        let timed = std::time::Instant::now();
        let _ = sampler.sample(fixture.pid());
        let one_sample = timed.elapsed();
        std::thread::sleep(std::time::Duration::from_millis(400));
        let second = sampler.sample(fixture.pid()).then(|| sampler.reading().to_vec());

        let leader = fixture.pid();
        let of = |reading: &[(u32, u64)], pid: u32| {
            reading.iter().find(|&&(seen, _)| seen == pid).map_or(0, |&(_, nanos)| nanos)
        };
        let total = |reading: &[(u32, u64)]| {
            reading.iter().fold(0_u64, |sum, &(_, nanos)| sum.saturating_add(nanos))
        };
        let first = first.expect("a tree with a live root must be sampleable");
        let second = second.expect("a tree with a live root must be sampleable twice");
        let spinner = spinner.expect("the fixture's descendant must report its pid");
        let spinner_group = libc::pid_t::try_from(spinner)
            .map(|spinner| unsafe { libc::getpgid(spinner) })
            .unwrap_or(-1);
        let advance = total(&second).saturating_sub(total(&first));
        let leader_advance = of(&second, leader).saturating_sub(of(&first, leader));

        // The fixture's own premise, established WITHOUT the walk under test:
        // the spinner is a descendant of the driver and is not in the driver's
        // process group. A group walk therefore cannot see any of the CPU
        // asserted below, whatever it reports.
        assert_ne!(
            spinner_group, leader as libc::pid_t,
            "the fixture must put its spinning descendant outside the driver's process group"
        );
        // A pinned core over 400ms of wall clock; a tenth of that is a floor no
        // scheduler noise reaches.
        assert!(
            advance >= 40_000_000,
            "a spinning descendant outside the driver's group must show consumed CPU, saw {advance}ns"
        );
        // The discriminator, stated rather than implied: essentially none of
        // that CPU is inside the group a group walk would have measured, so a
        // group walk here reads a busy tree as idle.
        assert!(
            leader_advance < super::CompilerCpuLiveness::nanos(super::COMPILER_CPU_ADVANCE_MIN),
            "the driver itself must be idle, so the observed CPU can only have come from \
             outside its process group; saw {leader_advance}ns"
        );
        eprintln!("one process-tree CPU sample over {} members took {one_sample:?}", second.len());
        assert!(
            one_sample < std::time::Duration::from_millis(5),
            "a CPU sample must be cheap enough to be unconditional, took {one_sample:?}"
        );
    }

    /// The other half of the same measurement. A sum over the members that are
    /// LIVE at each sample is not monotone, so it can FALL while the tree works
    /// flat out: measured on a live check on 2026-09-09 it went 6,835.4s ->
    /// 4,257.1s across one minute of twelve busy cores, purely because
    /// compilers finished and left. Under a rule of the form "the summed CPU of
    /// the live set advanced", that minute reads as no advance at all --
    /// exactly when the build is completing the most units.
    ///
    /// This fixture is that shape at test speed: a burner that accumulates real
    /// CPU and then exits while a sibling keeps the tree alive. The naive live
    /// sum must be seen to fall, and the accumulated total must not.
    ///
    /// Every step is armed on what the fixture has DONE, never on how long it
    /// was given. The burner is killed once it has been seen to have burned
    /// `BURNED`, and the second reading is taken once it has been seen to be
    /// gone from the tree: on a machine at load 26-38 a fixed 300ms gave the
    /// burner under 40ms of CPU in 12 runs of 30 (measured 2026-10-13), and
    /// the fall this test exists to show was then smaller than it asks for.
    /// And every live sum is one of the accumulator's OWN samples. Its total
    /// can only hold what it saw: a live sum read by a second sampler after
    /// the accumulator's reading counts CPU the burner went on to consume in
    /// between (15-182us in 4 whole runs of 10, same day), which no
    /// accumulator could have banked.
    ///
    /// A total that merely refused to fall would pass all of that, the burner
    /// being the last thing in the tree to have done any work. So the leader,
    /// which until then only waits, is told to work on (a line on its standard
    /// input), and once it has been seen to, a third reading must be the
    /// burner's last reading ON TOP of the live sum, which by then is more
    /// than the largest live sum there ever was can account for.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn cpu_accumulator_holds_the_work_of_a_member_that_exits() {
        use std::io::Write as _;

        /// What the naive live sum must be seen to fall by.
        const FALL: std::time::Duration = std::time::Duration::from_millis(40);
        /// What the burner must have burned before it is killed: three times
        /// the fall, so nothing the leader and the sleeper consume meanwhile
        /// can close the gap.
        const BURNED: std::time::Duration = std::time::Duration::from_millis(120);
        /// What the leader must be seen to consume after the burner is gone.
        const WORKED_ON: std::time::Duration = std::time::Duration::from_millis(20);
        /// A hang detector, not a latency budget: an unloaded machine arms in
        /// about `BURNED`, and each wait below ends on the state it waits for.
        const HANG: std::time::Duration = std::time::Duration::from_secs(60);
        const POLL: std::time::Duration = std::time::Duration::from_millis(5);

        // The leader waits for the burner alone, so it reaps it as soon as it
        // dies; then it blocks on its standard input until this test writes a
        // line, and only then does it consume CPU of its own. The sibling
        // sleeps well past every `HANG` below, so it is still in the tree
        // however long the waits take; `Drop` ends it.
        let mut command = std::process::Command::new("/bin/sh");
        command.args([
            "-c",
            "(while :; do :; done) & burner=$!; sleep 300 & wait \"$burner\"; read go; \
             while :; do :; done",
        ]);
        command.stdin(std::process::Stdio::piped()).stderr(std::process::Stdio::null());
        super::CompilerProcessGuard::configure(&mut command);
        let mut fixture = GroupFixture(command.spawn().expect("spawn group fixture"));
        let go = fixture.0.stdin.take();
        let leader = fixture.pid();
        let mut accumulator = super::CompilerCpuAccumulator::new();
        let total = |reading: &[(u32, u64)]| {
            reading.iter().fold(0_u64, |sum, &(_, nanos)| sum.saturating_add(nanos))
        };
        let of = |reading: &[(u32, u64)], pid: u32| {
            reading.iter().find(|&&(seen, _)| seen == pid).map(|&(_, nanos)| nanos)
        };

        // The burner is the member with the most CPU that is not the leader;
        // the leader only waits, and its sibling only sleeps, so neither ever
        // reaches `BURNED`. Every reading is captured before any assertion is
        // made, so no failure path can escape the fixture's `Drop`.
        let mut sampler = super::ProcessTreeCpuSampler::new();
        let mut busiest = None;
        let armed = std::time::Instant::now();
        let burner = loop {
            if sampler.sample(leader) {
                busiest = sampler
                    .reading()
                    .iter()
                    .filter(|&&(pid, _)| pid != leader)
                    .max_by_key(|&&(_, nanos)| nanos)
                    .copied();
            }
            match busiest {
                Some((pid, nanos)) if nanos >= super::CompilerCpuLiveness::nanos(BURNED) => {
                    break Some(pid);
                }
                _ if armed.elapsed() >= HANG => break None,
                _ => std::thread::sleep(POLL),
            }
        };
        let accumulated_before = accumulator.observe(leader);
        let seen_before = accumulator.sampler.reading().to_vec();
        let mut gone = false;
        if let Some(burner) = burner {
            if let Ok(burner) = libc::pid_t::try_from(burner) {
                let _ = unsafe { libc::kill(burner, libc::SIGKILL) };
            }
            // Until the tree no longer holds it. Its death alone is not
            // enough everywhere: Linux reads a zombie's CPU until the leader's
            // `wait` has reaped it, which is what actually removes it.
            let killed = std::time::Instant::now();
            while !gone && killed.elapsed() < HANG {
                gone = sampler.sample(leader)
                    && !sampler.reading().iter().any(|&(pid, _)| pid == burner);
                if !gone {
                    std::thread::sleep(POLL);
                }
            }
        }
        let accumulated_after = accumulator.observe(leader);
        let seen_after = accumulator.sampler.reading().to_vec();
        let mut worked_on = false;
        if let (true, Some(mut go), Some(leader_after)) = (gone, go, of(&seen_after, leader)) {
            let _ = go.write_all(b"go\n");
            let enough = leader_after.saturating_add(super::CompilerCpuLiveness::nanos(WORKED_ON));
            let told = std::time::Instant::now();
            while !worked_on && told.elapsed() < HANG {
                worked_on = sampler.sample(leader)
                    && of(sampler.reading(), leader).is_some_and(|now| now >= enough);
                if !worked_on {
                    std::thread::sleep(POLL);
                }
            }
        }
        let accumulated_final = accumulator.observe(leader);
        let seen_final = accumulator.sampler.reading().to_vec();

        let burner = burner.unwrap_or_else(|| {
            panic!(
                "the fixture's burner never showed {BURNED:?} of consumed CPU within {HANG:?}; the \
                 busiest member seen that is not the leader was {busiest:?} (pid, nanoseconds)"
            )
        });
        assert!(gone, "burner {burner} was still in the tree {HANG:?} after its SIGKILL");
        assert!(
            worked_on,
            "the fixture's leader never showed {WORKED_ON:?} more consumed CPU within {HANG:?} of \
             being told to work on"
        );
        let accumulated_before = accumulated_before.expect("the tree must be sampleable");
        let accumulated_after = accumulated_after.expect("the tree must be sampleable twice");
        let accumulated_final = accumulated_final.expect("the tree must be sampleable three times");
        let live_before = std::time::Duration::from_nanos(total(&seen_before));
        let live_after = std::time::Duration::from_nanos(total(&seen_after));
        let live_final = std::time::Duration::from_nanos(total(&seen_final));
        let burner_seen =
            of(&seen_before, burner).expect("the accumulator's first sample must hold the burner");

        // First that the fixture actually reproduced the condition: without a
        // real fall there is nothing here to be immune to.
        assert!(
            live_after + FALL <= live_before,
            "the fixture must make the naive live sum FALL, saw {live_before:?} -> {live_after:?} \
             after killing burner {burner}"
        );
        assert!(
            accumulated_after >= accumulated_before && accumulated_final >= accumulated_after,
            "the accumulated total must never fall, saw {accumulated_before}ns -> \
             {accumulated_after}ns -> {accumulated_final}ns"
        );
        // And it must have kept the work, not merely refused to go backwards:
        // everything the burner did is still in the total after it is gone.
        assert!(
            accumulated_after >= super::CompilerCpuLiveness::nanos(live_before),
            "the accumulated total must retain the CPU of a member that exited, saw \
             {accumulated_after}ns against a peak live sum of {live_before:?}"
        );
        // Which a total that only ever rose to the largest live sum would also
        // satisfy, until a survivor has worked on. It has:
        assert!(
            live_final >= live_after + WORKED_ON,
            "the fixture must make a survivor work on after the burner is gone, saw the live sum \
             go {live_after:?} -> {live_final:?}"
        );
        // so the total is now, to the nanosecond, what the burner had when the
        // accumulator last saw it on top of everything the members still in
        // the tree have consumed. To the nanosecond, so from above too: the
        // burner is the only member that leaves the tree, so a total above
        // this has counted some CPU twice.
        assert_eq!(
            accumulated_final,
            burner_seen.saturating_add(total(&seen_final)),
            "the accumulated total must be the exited member's last reading ({burner_seen}ns) on \
             top of the live sum ({live_final:?}), no less and no more"
        );
    }

    /// A watchdog that kills the driver and orphans its compilers is worse than
    /// no watchdog. Measured on 2026-09-09 that is exactly what the group kill
    /// did: the driver died and `ny_propagate` survived it on pid 1 at 99.8% of
    /// a core with 14.6 GB resident for twelve more minutes, holding a memory
    /// grant nothing would ever release, and then exited having written no
    /// artifact.
    ///
    /// This fixture carries both shapes at once -- one descendant inside the
    /// driver's process group, one outside it -- because the tree kill must add
    /// the second without losing the first. Survival is proved the way
    /// `bounded_process` proves it: a killed process can linger briefly as a
    /// zombie, for which `kill(pid, 0)` misleadingly succeeds, so the test asks
    /// whether either descendant could still EXECUTE.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn watchdog_kill_reaches_a_compiler_that_left_the_drivers_process_group() {
        let inside =
            std::env::temp_dir().join(format!("trust-tree-kill-inside-{}", std::process::id()));
        let outside =
            std::env::temp_dir().join(format!("trust-tree-kill-outside-{}", std::process::id()));
        let _ = std::fs::remove_file(&inside);
        let _ = std::fs::remove_file(&outside);
        let pid_path =
            std::env::temp_dir().join(format!("trust-tree-kill-pid-{}", std::process::id()));
        let _ = std::fs::remove_file(&pid_path);
        let fixture = IsolatedDescendantFixture::spawn(
            &format!("trap '' HUP; (sleep 1; printf survived > '{}') & wait", inside.display()),
            &format!("trap '' HUP; sleep 1; printf survived > '{}'", outside.display()),
            &pid_path,
        );
        // Established without the walk under test, for the same reason as in
        // `cpu_sample_follows_the_tree_out_of_the_drivers_process_group`: the
        // mutation must fail this test on its claim, not on its premise.
        let escaped = fixture_pid(&pid_path, std::time::Duration::from_secs(5));
        let _ = std::fs::remove_file(&pid_path);
        let leader = fixture.pid();
        let escaped_group = escaped
            .and_then(|pid| libc::pid_t::try_from(pid).ok())
            .map(|pid| unsafe { libc::getpgid(pid) })
            .unwrap_or(-1);
        // Both descendants exist well before their markers are due.
        std::thread::sleep(std::time::Duration::from_millis(300));
        let killed = crate::process_lifecycle::stop_tree(
            leader,
            crate::process_lifecycle::StopCause::Backstop,
        );
        // Past the markers' one-second delay, so a survivor has had its chance.
        std::thread::sleep(std::time::Duration::from_millis(1_400));
        let inside_survived = inside.exists();
        let outside_survived = outside.exists();
        let _ = std::fs::remove_file(&inside);
        let _ = std::fs::remove_file(&outside);

        assert!(escaped.is_some(), "the fixture's descendant must report its pid");
        assert_ne!(
            escaped_group, leader as libc::pid_t,
            "the fixture must put its escaping descendant outside the driver's process group"
        );
        killed.expect("the driver's own process group must still be killed");
        assert!(
            !inside_survived,
            "a descendant INSIDE the driver's process group survived the kill -- the tree walk \
             must not have cost the group kill anything"
        );
        assert!(
            !outside_survived,
            "a compiler OUTSIDE the driver's process group survived the kill and would have been \
             orphaned onto pid 1, which is the defect this walk exists to fix"
        );
    }

    const DAEMON_STAND_IN_PID_ENV: &str = "TARGO_TRUST_TEST_DAEMON_STAND_IN_PID";
    const DAEMON_STAND_IN_MARKER_ENV: &str = "TARGO_TRUST_TEST_DAEMON_STAND_IN_MARKER";

    /// Not a test: the body of the stand-in `trustd` that
    /// `watchdog_never_samples_or_kills_a_trustd_inside_the_tree` runs, as a
    /// copy of this test binary named `trustd`. Without its environment it
    /// does nothing, so `--ignored` runs stay harmless.
    #[test]
    #[ignore = "stand-in process body for watchdog_never_samples_or_kills_a_trustd_inside_the_tree"]
    fn trust_memory_daemon_stand_in() {
        let (Some(pid_path), Some(marker)) = (
            std::env::var_os(DAEMON_STAND_IN_PID_ENV),
            std::env::var_os(DAEMON_STAND_IN_MARKER_ENV),
        ) else {
            return;
        };
        std::fs::write(&pid_path, std::process::id().to_string()).expect("report stand-in pid");
        // Long enough for the test to sample and kill the tree first; the
        // marker is written only by a stand-in that is still alive after it.
        std::thread::sleep(std::time::Duration::from_millis(1_500));
        std::fs::write(&marker, "survived").expect("write survival marker");
    }

    /// The machine-wide `trustd` is the memory authority for every verified
    /// build on the host, and it leads a process group of its own (41f912aa5f)
    /// -- exactly the shape of a compiler the tree walk exists to follow. A
    /// nested `targo trust` that starts the daemon makes it a descendant of the
    /// driver, so the walk must recognise it by its executable image and leave
    /// it, and everything under it, out of both the sample and the kill.
    ///
    /// The stand-in is a copy of THIS test binary named `trustd` (a copied
    /// system binary is refused by macOS launch constraints), isolated in its
    /// own group, running `trust_memory_daemon_stand_in`. It needs no cleanup
    /// signal: it exits on its own once its marker is written.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn watchdog_never_samples_or_kills_a_trustd_inside_the_tree() {
        let dir = std::env::temp_dir().join(format!(
            "trust-tree-daemon-{}-{}",
            std::process::id(),
            line!()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("fixture directory");
        let daemon = dir.join("trustd");
        std::fs::copy(std::env::current_exe().expect("test binary"), &daemon)
            .expect("copy the test binary as trustd");
        let survived = dir.join("survived");
        let pid_path = dir.join("pid");
        let filter = format!("{}::trust_memory_daemon_stand_in", module_path!());
        // The harness names tests without the crate prefix.
        let filter = filter.split_once("::").map_or(filter.as_str(), |(_, rest)| rest).to_string();
        let fixture = IsolatedDescendantFixture::spawn_with_descendant(
            &daemon,
            &["trustd", "--exact", &filter, "--ignored", "--test-threads=1", "--quiet"],
            &[
                (DAEMON_STAND_IN_PID_ENV, pid_path.as_os_str()),
                (DAEMON_STAND_IN_MARKER_ENV, survived.as_os_str()),
            ],
            "trap '' HUP; sleep 30 & wait",
        );
        let daemon_pid = fixture_pid(&pid_path, std::time::Duration::from_secs(20));
        let leader = fixture.pid();
        let recognised = daemon_pid.map(super::is_trust_memory_daemon);
        let leader_recognised = super::is_trust_memory_daemon(leader);
        let mut tree = Vec::new();
        let enumerated = super::collect_process_tree(leader, &mut tree);
        let killed = crate::process_lifecycle::stop_tree(
            leader,
            crate::process_lifecycle::StopCause::Backstop,
        );
        // Past the stand-in's delay, so a survivor has had its chance.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while !survived.exists() && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        let daemon_survived = survived.exists();
        drop(fixture);
        let _ = std::fs::remove_dir_all(&dir);

        let daemon_pid = daemon_pid.expect("the stand-in daemon must report its pid");
        assert_eq!(recognised, Some(true), "the stand-in must be recognised by its image");
        assert!(!leader_recognised, "the driver is never the daemon");
        assert!(enumerated, "the tree must still be enumerable");
        assert!(tree.contains(&leader), "the driver is the root of its own tree");
        assert!(
            !tree.contains(&daemon_pid),
            "trustd must never be sampled as compiler work: {tree:?} contains {daemon_pid}"
        );
        killed.expect("the driver's own process group must still be killed");
        assert!(
            daemon_survived,
            "the watchdog's tree kill reached the machine-wide trustd -- every verified gate on \
             the host would refuse to start until an operator recovered its epoch"
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn trust_memory_daemon_identity_is_the_image_file_name() {
        use std::path::Path;
        assert!(super::executable_is_trust_memory_daemon(Path::new("/opt/trust/bin/trustd")));
        assert!(super::executable_is_trust_memory_daemon(Path::new(
            "/opt/trust/bin/trustd (deleted)"
        )));
        assert!(!super::executable_is_trust_memory_daemon(Path::new("/opt/trust/bin/trustc")));
        assert!(!super::executable_is_trust_memory_daemon(Path::new("/opt/trustd/bin/rustc")));
        assert!(!super::executable_is_trust_memory_daemon(Path::new("/opt/bin/trustd-helper")));
        // This test process is not the daemon, and its image is readable.
        assert!(!super::is_trust_memory_daemon(std::process::id()));
    }

    /// The case this guard was weakened by: cargo has been talking, one unit
    /// dies, cargo stops scheduling and waits out its in-flight jobs, and those
    /// jobs compute in silence. Output says "stalled"; CPU says "working". The
    /// idle bound must not fire, and the only thing that may stop this fixture
    /// is the absolute ceiling.
    ///
    /// Every bound here is shorter than the fixture's own lifetime, so
    /// outliving the idle bound is possible ONLY through the CPU signal.
    #[cfg(unix)]
    #[test]
    fn compiler_burning_cpu_without_output_outlives_the_idle_bound() {
        let (outcome, elapsed) = run_drained_fixture(
            "echo diagnostic >&2; (while :; do :; done) & wait",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_secs(30),
                idle: std::time::Duration::from_millis(400),
                absolute: std::time::Duration::from_secs(2),
            },
        );
        let error = outcome.expect_err("the absolute ceiling still stops an endless spinner");
        assert!(error.contains("absolute bound"), "{error}");
        assert!(error.contains("of CPU consumed"), "{error}");
        assert!(
            elapsed >= std::time::Duration::from_millis(1800),
            "a compiler consuming CPU must outlive the 400ms idle bound: {elapsed:?}"
        );
        assert!(elapsed < std::time::Duration::from_secs(10), "absolute bound was not enforced");
    }

    /// The other half of the same rule, and the reason the CPU signal cannot
    /// simply be trusted to keep things alive: one diagnostic to arm the idle
    /// regime, then a process group that neither writes nor computes. The idle
    /// bound must still fire, and the message must now say BOTH things were
    /// stale rather than only naming the output clock.
    #[cfg(unix)]
    #[test]
    fn compiler_that_neither_writes_nor_burns_cpu_dies_at_the_idle_bound() {
        let (outcome, elapsed) = run_drained_fixture(
            "echo diagnostic >&2; sleep 30 & wait",
            super::CompilerProcessBounds {
                silent: std::time::Duration::from_secs(30),
                idle: std::time::Duration::from_millis(400),
                absolute: std::time::Duration::from_secs(3),
            },
        );
        let error = outcome.expect_err("a compiler doing nothing at all must be killed");
        assert!(error.contains("stopped making progress"), "{error}");
        assert!(error.contains("idle bound"), "{error}");
        // Not just "the CPU clock was stale": the sample must have SUCCEEDED,
        // or this test would pass on a platform where the feature is absent.
        assert!(error.contains("consumed no CPU for"), "{error}");
        assert!(error.contains("having consumed"), "{error}");
        assert!(
            elapsed < std::time::Duration::from_secs(2),
            "the idle bound must still fire on a group burning no CPU: {elapsed:?}"
        );
    }

    fn package(name: &str, id: &str) -> ResolvedCargoPackage {
        ResolvedCargoPackage {
            id: id.to_string(),
            name: name.to_string(),
            root: PathBuf::from(format!("/workspace/{name}")),
        }
    }

    fn selection(packages: Vec<ResolvedCargoPackage>) -> ResolvedCargoSelection {
        ResolvedCargoSelection {
            packages,
            resolved_packages: std::collections::BTreeSet::new(),
            target_directory: PathBuf::from("/workspace/target"),
        }
    }

    #[test]
    fn manifest_path_arg_handles_both_spellings() {
        assert_eq!(
            cargo_manifest_path_arg(&s(&["build", "--manifest-path", "crates/x/Cargo.toml"])),
            Some(std::path::PathBuf::from("crates/x/Cargo.toml"))
        );
        assert_eq!(
            cargo_manifest_path_arg(&s(&["build", "--manifest-path=a/Cargo.toml"])),
            Some(std::path::PathBuf::from("a/Cargo.toml"))
        );
        assert_eq!(cargo_manifest_path_arg(&s(&["build"])), None);
    }

    #[test]
    fn custom_target_tcb_rejects_oversized_input_before_json_parsing() {
        let root = tempfile::tempdir().expect("custom target fixture");
        let target = root.path().join("oversized.json");
        let file = std::fs::File::create(&target).expect("create target");
        file.set_len(crate::input_limits::MAX_RELEASE_METADATA_BYTES as u64 + 1)
            .expect("oversize target");
        let error = validate_direct_custom_target_extension_tcb(
            target.to_str().expect("UTF-8 target path"),
        )
        .expect_err("oversized custom target must fail closed");
        assert!(error.contains("safety limit"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn custom_target_tcb_rejects_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("custom target fixture");
        let target = root.path().join("target.json");
        let linked = root.path().join("linked.json");
        std::fs::write(&target, "{}").expect("write target");
        symlink(&target, &linked).expect("link target");
        let error = validate_direct_custom_target_extension_tcb(
            linked.to_str().expect("UTF-8 target path"),
        )
        .expect_err("symlinked custom target must fail closed");
        assert!(error.contains("not a regular file"), "{error}");
    }

    #[test]
    fn raw_ambient_verifier_controls_are_removed_from_child_processes() {
        let mut command = std::process::Command::new("unused");
        command.env("TRUST_VERIFY", "1");
        command.env("TRUST_DUMP_ONLY", "1");
        command.env("TRUST_NO_VERIFY", "1");
        scrub_proof_compiler_authority_env(&mut command);
        for removed in ["TRUST_VERIFY", "TRUST_DUMP_ONLY", "TRUST_NO_VERIFY"] {
            assert!(
                command.get_envs().any(|(name, value)| {
                    name == std::ffi::OsStr::new(removed) && value.is_none()
                })
            );
        }
    }

    #[test]
    fn test_monitor_marker_is_session_bound_and_test_only() {
        let mut test_command = std::process::Command::new("unused");
        apply_targo_test_monitor_session(&mut test_command, true, "fresh-test-session");
        assert!(test_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION")
                && value == Some(std::ffi::OsStr::new("fresh-test-session"))
        }));

        let mut build_command = std::process::Command::new("unused");
        build_command.env("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION", "ambient");
        apply_targo_test_monitor_session(&mut build_command, false, "fresh-build-session");
        assert!(build_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION")
                && value.is_none()
        }));
    }

    #[test]
    fn cargo_child_pins_both_compiler_configuration_spellings() {
        let mut command = std::process::Command::new("unused");
        let compiler = std::path::Path::new("/authenticated/toolchain/trustc");
        apply_cargo_child_rustc_env(&mut command, compiler);
        let envs = command.get_envs().collect::<Vec<_>>();
        for name in ["RUSTC", "CARGO_BUILD_RUSTC"] {
            assert!(envs.iter().any(|(key, value)| {
                *key == std::ffi::OsStr::new(name)
                    && value.is_some_and(|value| value == compiler.as_os_str())
            }));
        }
    }

    #[test]
    fn trust_cg_cargo_policy_disables_incremental_before_unit_construction() {
        let mut command = std::process::Command::new("unused");
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: "trust-cg-incremental-test",
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: None,
        };
        apply_lane_flags_env(LaneFlagsInput {
            cmd: &mut command,
            config: &TrustConfig::default(),
            selected_codegen_backend: Some("trust-cg"),
            supports_json_transport: true,
            strict_artifact_policy: true,
            allow_l0_gaps: false,
            controls: &controls,
            requirements: &ProjectRequirementFlags::default(),
            cargo_args: &[],
        })
        .expect("configure trust-cg Cargo environment");
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("CARGO_INCREMENTAL")
                && value == Some(std::ffi::OsStr::new("0"))
        }));
    }

    /// S9: the stderr of a `-Ztrust-verify=off` unit built with an external
    /// backend is not evidence that verification ran, in either mode, even
    /// when it ends with a zero crate summary and a Kani SUCCESSFUL line.
    #[test]
    fn external_backend_verify_off_unit_is_not_evidence_that_verification_ran() {
        for stderr in [
            crate::pipeline::kani_gate::EXTERNAL_BACKEND_VERIFY_OFF_STDERR,
            crate::pipeline::kani_gate::EXTERNAL_BACKEND_VERIFY_OFF_STDERR_WITH_ZERO_SUMMARY,
        ] {
            let parsed =
                crate::pipeline::parse_compiler_stderr(std::io::Cursor::new(stderr), false);
            for crate_mode in [false, true] {
                assert!(
                    super::missing_trust_json_diagnostic(
                        crate_mode,
                        &parsed.verification_results,
                        &std::collections::BTreeSet::new(),
                        !parsed.coverage_rows.is_empty(),
                    )
                    .is_some(),
                    "an external-backend verify-off unit passed the verification-ran gate \
                     (crate_mode={crate_mode})"
                );
            }
        }
    }

    /// RAII environment override, serialized by `crate::TEST_ENV_LOCK` the way
    /// `pipeline::probe`'s tests are: the lane assembly below reads the
    /// ambient RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS (to name ignored `-Ztrust-*`
    /// options), so it cannot race another test mutating them.
    struct RustflagsEnvGuard {
        key: &'static str,
        old: Option<std::ffi::OsString>,
    }

    impl RustflagsEnvGuard {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired TEST_ENV_LOCK); the single audited boundary.
        fn set(key: &'static str, value: &str) -> Self {
            let old = env::var_os(key);
            env::set_var(key, value);
            Self { key, old }
        }

        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired TEST_ENV_LOCK); the single audited boundary.
        fn unset(key: &'static str) -> Self {
            let old = env::var_os(key);
            env::remove_var(key);
            Self { key, old }
        }
    }

    impl Drop for RustflagsEnvGuard {
        #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired TEST_ENV_LOCK); the single audited boundary.
        fn drop(&mut self) {
            if let Some(old) = self.old.take() {
                env::set_var(self.key, old);
            } else {
                env::remove_var(self.key);
            }
        }
    }

    /// Read back the lane this run hands the child Cargo
    /// (`TRUST_TARGO_LANE_RUSTFLAGS`, always Cargo's encoded form).
    fn exported_lane(command: &std::process::Command) -> Vec<String> {
        let value = command
            .get_envs()
            .find_map(|(key, value)| {
                (key == std::ffi::OsStr::new(TRUST_TARGO_LANE_RUSTFLAGS_ENV)).then_some(value)
            })
            .flatten()
            .expect("no lane was handed to the child Cargo");
        let value = value.to_str().expect("the lane is UTF-8");
        if value.is_empty() {
            Vec::new()
        } else {
            value.split('\x1f').map(str::to_string).collect()
        }
    }

    /// Whether this run touched one of the caller's rustflags variables on
    /// the child Cargo's command (T14a: it never does).
    fn sets_or_removes(command: &std::process::Command, name: &str) -> bool {
        command.get_envs().any(|(key, _)| key == std::ffi::OsStr::new(name))
    }

    /// Whether the lane carries a `-Ztrust-verify` **activation**
    /// option, in any of the spellings rustc accepts (`-Z name=value`,
    /// `-Zname=value`, `_`-for-`-`). Deliberately compares the canonical option
    /// NAME rather than substring-matching: the tracked policy legitimately
    /// contains `trust-verify-session`, `trust-verify-level`,
    /// `trust-verify-output` and friends, none of which is the off-switch.
    fn carries_verification_activation_option(args: &[String]) -> bool {
        let mut index = 0;
        while index < args.len() {
            let option = if args[index] == "-Z" {
                index += 1;
                args.get(index).map(String::as_str)
            } else {
                args[index].strip_prefix("-Z").filter(|option| !option.is_empty())
            };
            if option.is_some_and(|option| canonical_rustc_option_name(option) == "trust-verify") {
                return true;
            }
            index += 1;
        }
        false
    }

    /// The verification opt-out is scoped PER COMPILATION UNIT, and targo-trust
    /// owns the half of that contract that lives in rustflags.
    ///
    /// `-Ztrust-verify=off` is the compiler's only off-switch, and RUSTFLAGS
    /// reaches every unit Cargo builds — the workspace crate, every third-party
    /// dependency, every build script and proc macro. Applying the opt-out
    /// there is precisely what forces the `=on` enable value to exist: once a
    /// build has been switched off wholesale, something has to switch it back
    /// on for the one crate that was supposed to be proved.
    ///
    /// So the scoping lives one layer down, in the sibling `targo`'s own
    /// per-Unit engine (`trust_unit_verification_enabled` /
    /// `trust_unit_protocol_args` in
    /// `src/tools/targo/src/cargo/core/compiler/mod.rs`): Targo appends
    /// `-Ztrust-verify=off` *after* every caller-controlled flag source, on
    /// exactly the Units that are neither a resolved proof root nor a
    /// test-execution subject (build scripts are never proof roots), and hashes
    /// that decision into the Cargo fingerprint
    /// (`fingerprint::calculate`'s `targo-trust-unit-scope-v5` tuple) so a warm
    /// cache can never serve a scoped-out artifact as a verified one.
    ///
    /// What targo-trust must guarantee is the other half: the run-level
    /// lane carries the tracked `-Ztrust-verify-session` nonce — the
    /// evidence hook `missing_trust_json_diagnostic` names — and carry NO
    /// verification activation token in either direction, so the compiler's
    /// batteries-on default governs every unit Targo did not explicitly scope
    /// out. If dependency scoping is ever "simplified" back into these
    /// rustflags, the authenticated primary target silently stops being
    /// verified and only `-Ztrust-verify=on` could claw it back.
    #[test]
    fn verification_opt_out_is_never_applied_graph_wide_through_rustflags() {
        let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: None,
        };
        let configure = |command: &mut std::process::Command| {
            apply_lane_flags_env(LaneFlagsInput {
                cmd: command,
                config: &TrustConfig::default(),
                selected_codegen_backend: None,
                supports_json_transport: true,
                strict_artifact_policy: true,
                allow_l0_gaps: false,
                controls: &controls,
                requirements: &ProjectRequirementFlags::default(),
                cargo_args: &[],
            })
            .expect("assemble verified Cargo rustflags");
        };

        // 1. Clean environment: the tracked nonce reaches the compiler through
        //    the lane, nothing turns verification off or on, and the caller's
        //    rustflags variables are not touched.
        {
            let _plain = RustflagsEnvGuard::unset("RUSTFLAGS");
            let _encoded = RustflagsEnvGuard::unset("CARGO_ENCODED_RUSTFLAGS");
            let mut command = std::process::Command::new("unused");
            configure(&mut command);
            let lane = exported_lane(&command);
            assert!(
                lane.windows(2).any(|pair| pair[0] == "-Z"
                    && pair[1] == format!("trust-verify-session={}", session.id)),
                "the tracked session nonce must reach the authenticated primary target: {lane:?}"
            );
            assert!(
                !carries_verification_activation_option(&lane),
                "targo-trust applied a graph-wide verification switch: {lane:?}"
            );
            for name in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"] {
                assert!(!sets_or_removes(&command, name), "{name} was rewritten");
            }
        }

        // 2. The caller's encoded flags stay the caller's: the sibling Targo
        //    resolves them by Cargo's precedence and appends the same lane.
        {
            let _plain = RustflagsEnvGuard::unset("RUSTFLAGS");
            let _encoded = RustflagsEnvGuard::set("CARGO_ENCODED_RUSTFLAGS", "-C\x1fopt-level=2");
            let mut command = std::process::Command::new("unused");
            configure(&mut command);
            let lane = exported_lane(&command);
            assert!(!lane.iter().any(|arg| arg == "opt-level=2"), "{lane:?}");
            assert!(!carries_verification_activation_option(&lane), "{lane:?}");
            assert!(!sets_or_removes(&command, "CARGO_ENCODED_RUSTFLAGS"));
        }

        // 3. `-Ztrust-verify=on` — the flag a too-coarse opt-out forces callers
        //    to invent — has no route into this lane: the lane is built from
        //    the tracked policy alone, the sibling Targo drops every
        //    environment `-Ztrust-*` token, and targo trust surfaces it with the
        //    per-run selections, so it can never re-widen a scope Targo
        //    resolved from the Cargo unit graph.
        {
            let _encoded = RustflagsEnvGuard::unset("CARGO_ENCODED_RUSTFLAGS");
            let _plain = RustflagsEnvGuard::set("RUSTFLAGS", "-C opt-level=2 -Ztrust-verify=on");
            let mut command = std::process::Command::new("unused");
            configure(&mut command);
            let lane = exported_lane(&command);
            assert!(
                !carries_verification_activation_option(&lane),
                "an ambient enable value reached the lane: {lane:?}"
            );
            assert!(!sets_or_removes(&command, "RUSTFLAGS"), "the caller's flags are theirs");
            let warning = inherited_trust_rustflags_warning(None, Some("-Ztrust-verify=on"))
                .expect("a stripped ambient trust option must be surfaced, not silent");
            assert!(warning.contains("-Ztrust-verify=on"), "{warning}");
            assert!(warning.contains(super::super::backend::PER_RUN_SELECTIONS), "{warning}");
        }

        // 4. The off-switch is not merely stripped from RUSTFLAGS: it is a hard
        //    error before any compiler is spawned, in both representations. A
        //    caller that believes it disabled verification must never receive a
        //    report that claims it ran.
        {
            let _encoded = RustflagsEnvGuard::unset("CARGO_ENCODED_RUSTFLAGS");
            let _plain = RustflagsEnvGuard::set("RUSTFLAGS", "-Ztrust-verify=off");
            let diagnostic = trust_verify_disable_diagnostic(&[], false)
                .expect("an ambient graph-wide opt-out must fail closed");
            assert!(
                diagnostic.contains("RUSTFLAGS contains `-Z trust-verify=off`"),
                "{diagnostic}"
            );
        }
        {
            let _plain = RustflagsEnvGuard::unset("RUSTFLAGS");
            let _encoded =
                RustflagsEnvGuard::set("CARGO_ENCODED_RUSTFLAGS", "-Z\x1ftrust_verify=off");
            let diagnostic = trust_verify_disable_diagnostic(&[], false)
                .expect("an ambient encoded graph-wide opt-out must fail closed");
            assert!(
                diagnostic.contains("CARGO_ENCODED_RUSTFLAGS contains `-Z trust-verify=off`"),
                "{diagnostic}"
            );
        }

        // 5. There is no per-run channel left to smuggle one through: TRUSTFLAGS
        //    is not read (T7a), and a project requirement is never an
        //    activation value (`ProjectTrustPolicy::options`).

        // 6. And not through `targo trust rustc -- <args>` passthrough.
        for flag in [
            vec!["-Ztrust-verify=off".to_string()],
            vec!["-Z".to_string(), "trust-verify=on".to_string()],
        ] {
            assert!(
                trust_verify_disable_diagnostic(&flag, true).is_some(),
                "passthrough activation value survived: {flag:?}"
            );
        }
    }

    /// Two verified runs hand Cargo lanes that differ ONLY in the
    /// per-run transport pair: `-Ztrust-verify-session` and
    /// `-Ztrust-proof-artifact-root`.
    ///
    /// Targo names each unit's artifacts and fingerprint directory with a
    /// `unit_id` hashed over these rustflags. For a unit it compiles with
    /// `-Ztrust-verify=off` (every dependency and build script outside the
    /// requested scope) it leaves this pair out, by the projection its
    /// fingerprint uses (`src/tools/targo/src/cargo/core/compiler/trust_unit_id.rs`),
    /// so an identical dependency is reused across checks in a kept target
    /// directory. That holds only while this side exports nothing else that
    /// changes from run to run: one more per-run value here would give every
    /// dependency a new identity on every check again, silently. The verified
    /// units keep the session in their key, so it must still be exported.
    #[test]
    fn two_sessions_differ_only_in_the_per_run_transport_pair() {
        let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
        let _plain = RustflagsEnvGuard::unset("RUSTFLAGS");
        let _encoded = RustflagsEnvGuard::unset("CARGO_ENCODED_RUSTFLAGS");
        let exported = |session: &VerificationSession, per_mille: u32| {
            let budget = trust_types::determinism::BudgetProfile::new(
                trust_types::determinism::EffortScale::BUILTIN,
                trust_types::determinism::Backstop { per_mille },
                0,
            );
            let controls = VerificationControls {
                policy: TrustPolicySelection::Strict,
                budget: &budget,
                hardened_profile: None,
                verification_session: &session.id,
                proof_artifact_root: session.artifact_root(),
                spec_emit_dir: None,
            };
            let mut command = std::process::Command::new("unused");
            apply_lane_flags_env(LaneFlagsInput {
                cmd: &mut command,
                config: &TrustConfig::default(),
                selected_codegen_backend: None,
                supports_json_transport: true,
                strict_artifact_policy: true,
                allow_l0_gaps: false,
                controls: &controls,
                requirements: &ProjectRequirementFlags::default(),
                cargo_args: &[],
            })
            .expect("assemble verified Cargo rustflags");
            let args = exported_lane(&command);
            // Split off the per-run pair, in either `-Z` spelling.
            let (mut kept, mut per_run) = (Vec::new(), Vec::new());
            let mut index = 0;
            while index < args.len() {
                let (option, consumed) = if args[index] == "-Z" {
                    (args.get(index + 1).map(String::as_str), 2)
                } else {
                    (args[index].strip_prefix("-Z"), 1)
                };
                let end = (index + consumed).min(args.len());
                match option.map(canonical_rustc_option_name).as_deref() {
                    Some("trust-verify-session" | "trust-proof-artifact-root") => {
                        per_run.push(option.unwrap_or_default().to_string());
                    }
                    _ => kept.extend_from_slice(&args[index..end]),
                }
                index = end;
            }
            (kept, per_run)
        };

        let first = VerificationSession::create().expect("create first session");
        let second = VerificationSession::create().expect("create second session");
        let (first_kept, first_per_run) = exported(&first, 1000);
        let (second_kept, second_per_run) = exported(&second, 1000);
        assert_eq!(
            first_kept, second_kept,
            "a second session changed an exported rustflag other than the per-run pair"
        );
        assert_eq!(
            first_per_run,
            [
                format!("trust-verify-session={}", first.id),
                format!("trust-proof-artifact-root={}", first.artifact_root().display()),
            ],
            "the verified units' session and artifact root must still be exported"
        );
        assert_ne!(first_per_run, second_per_run);

        // Negative control: a real verifier control is not per-run, and it
        // still reaches every unit's identity.
        let (changed_kept, _) = exported(&first, 1200);
        assert_ne!(changed_kept, first_kept, "a changed backstop must change the exported flags");
    }

    /// Every project requirement, the strictest a Cargo configuration can
    /// state, as `ProjectRequirementFlags` carries it to the compile.
    fn strictest_project_requirements() -> ProjectRequirementFlags {
        let policy = crate::pipeline::project_policy::ProjectTrustPolicy::parse(
            br#"{"schema":"trust.project-policy.v1","policy":"certify","level":2,"profile":"unix_hardened","include_dependencies":true,"ir_lower":"strict","verification_required":true}"#,
        )
        .expect("the strictest project policy parses");
        ProjectRequirementFlags::for_run(Some(&policy), "certify", Some("unix_hardened"), 2)
            .expect("an adopted run agrees with its requirements")
    }

    #[test]
    fn strict_lowering_requirements_are_typed_nonactivation_options() {
        // This transports nonactivation policy only. It does not license
        // configured host authority or the unsupported authenticated doctest
        // lane. The sibling Targo admits each into the lane only from its own
        // closed host-policy protocol (`TrustLane::new`).
        let parsed = strictest_project_requirements();
        assert_eq!(
            parsed.options(),
            [
                "trust-policy=certify",
                "trust-verify-level=2",
                "trust-verify-profile=unix_hardened",
                "trust-verify-include-dependencies=yes",
                "trust-ir-lower=strict",
            ]
        );
    }

    /// The lane is a GRAPH-WIDE channel, and the sibling Targo admits it only
    /// from a closed protocol (`VERIFIED_TARGO_HOST_POLICY_OPTIONS` /
    /// `extract_verified_targo_host_policy`, applied to the whole lane by
    /// `TrustLane::new` in
    /// `src/tools/targo/src/cargo/core/compiler/build_context/target_info.rs`,
    /// before any probe or unit exists): any `-Ztrust_*` option outside it,
    /// `-Ztrust-verify` in either direction included, refuses the run. That one
    /// list is the protocol; targo-trust keeps no copy of it (T14a). What this
    /// side owns is that the controls carry the evidence hook and the recorded
    /// worker-thread cap, and never the activation switch.
    #[test]
    fn verification_control_options_carry_the_session_and_never_the_activation_switch() {
        let session = VerificationSession::create().expect("create session");
        // Maximal controls: every optional option is populated, so the
        // allowlist is checked against the widest command line this run can
        // produce rather than the default one. `--worker-threads 3` reaches the
        // compiler through the profile that records it (T7a).
        let serial_budget = trust_types::determinism::BudgetProfile::new(
            BUILTIN_BUDGET.effort,
            BUILTIN_BUDGET.backstop,
            3,
        );
        let controls = VerificationControls {
            policy: TrustPolicySelection::Advisory,
            budget: &serial_budget,
            hardened_profile: Some("boundary"),
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: None,
        };

        for policy in [
            TrustPolicySelection::Strict,
            TrustPolicySelection::Certify,
            TrustPolicySelection::Advisory,
            TrustPolicySelection::MemorySafe,
        ] {
            let options =
                verification_control_options(&VerificationControls { policy, ..controls })
                    .expect("assemble verifier control options");
            // `trust-verify` is the load-bearing absence: it is the compiler's
            // sole verification switch, so carrying it here at all — in either
            // direction — is exactly the too-coarse opt-out that forces an
            // `=on` enable value to exist to claw the primary target back.
            for option in &options {
                assert_ne!(
                    canonical_rustc_option_name(option),
                    "trust-verify",
                    "verification scope is resolved per compilation Unit inside targo: {options:?}"
                );
            }
            // The evidence hook itself: without the tracked nonce the run has
            // no authenticated verification stream to authenticate at all.
            assert!(
                options
                    .iter()
                    .any(|option| option == &format!("trust-verify-session={}", session.id)),
                "the tracked session nonce must be part of every verified run: {options:?}"
            );
            assert_eq!(
                options
                    .iter()
                    .filter(|option| option.starts_with("trust-verify-worker-threads="))
                    .collect::<Vec<_>>(),
                ["trust-verify-worker-threads=3"],
                "the recorded worker-thread cap is the one passed: {options:?}"
            );
        }
        // The builtin profile caps nothing, and passes nothing (0 is the
        // compiler's own default).
        let uncapped = verification_control_options(&VerificationControls {
            budget: &BUILTIN_BUDGET,
            ..controls
        })
        .expect("assemble verifier control options");
        assert!(
            !uncapped.iter().any(|option| option.starts_with("trust-verify-worker-threads")),
            "{uncapped:?}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn unix_file_only_override_is_rejected_without_exporting_an_authority() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-env-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["build", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/tmp/attacker.sock");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "/tmp/attacker.tokens");
        let error = apply_crate_memory_coordination_with(
            &mut command,
            &args,
            None,
            None,
            false,
            |_| -> Result<(), &'static str> {
                panic!("disabled lane must not probe or start a daemon")
            },
            &SessionLease::new(),
        )
        .expect_err("Unix file-only mode must fail closed");
        // A configuration the caller chose is a setup error (2), not a daemon
        // that could not run the work (3).
        let ChildSetupError::Setup(error) = error else {
            panic!("a disabled lane is a setup error: {error:?}")
        };

        let envs = command.get_envs().collect::<Vec<_>>();
        assert!(envs.iter().any(|(name, value)| {
            *name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_ENV) && value.is_none()
        }));
        assert!(envs.iter().any(|(name, value)| {
            *name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV) && value.is_none()
        }));
        assert!(error.contains("file-only authority"));
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn healthy_unix_memory_domain_is_shared_across_target_directories() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-healthy-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let member = root.join("member");
        let target = root.join("metadata-target");
        let manifest = member.join("Cargo.toml");
        let args = s(&["check", "--manifest-path", manifest.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUSTD_DISABLE_ENV, "false");
        let expected = trust_router::coordinator::host_socket_path()
            .expect("private per-user trustd endpoint");
        apply_crate_memory_coordination_with(
            &mut command,
            &args,
            Some(&target),
            Some(std::ffi::OsStr::new("/tmp/inherited.tokens")),
            true,
            |socket| {
                (socket == expected)
                    .then_some(())
                    .ok_or("coordinator selected an unexpected socket")
            },
            &SessionLease::new(),
        )
        .expect("exact daemon is ready");
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV)
                && value == Some(expected.as_os_str())
        }));
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_ENV) && value.is_none()
        }));
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUSTD_DISABLE_ENV) && value.is_none()
        }));
        assert_ne!(expected, target.join("trust-memory-jobserver.sock"));
        assert_ne!(expected, member.join("target/trust-memory-jobserver.sock"));

        let other_target = root.join("independent-target");
        let other_args =
            s(&["check", "--target-dir", other_target.to_str().expect("UTF-8 temp path")]);
        let mut other_command = std::process::Command::new("unused");
        apply_crate_memory_coordination_with(
            &mut other_command,
            &other_args,
            Some(&other_target),
            None,
            true,
            |socket| {
                (socket == expected)
                    .then_some(())
                    .ok_or("coordinator selected an unexpected socket")
            },
            &SessionLease::new(),
        )
        .expect("independent target reuses exact host daemon");
        assert!(other_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV)
                && value == Some(expected.as_os_str())
        }));
        let _ = std::fs::remove_dir_all(root);
    }

    /// The half of the 0.11.0 fix (2026-10-19) that runs in targo-trust: the
    /// lease `ensure_daemon` returns must outlive this seam, because the units
    /// that use the socket it exports run afterwards, and one may compile for
    /// longer than the daemon's idle bound before its first admission. A
    /// re-application (a rewrite-loop iteration) takes its lease while the
    /// session still holds the earlier one, and drops that one only once its
    /// successor is stored.
    #[cfg(unix)]
    #[test]
    fn coordination_leaves_the_session_holding_its_trustd_lease() {
        // Every lease drop, with the lease the session held at that instant.
        static DROPS: std::sync::Mutex<Vec<(u8, Option<u8>)>> = std::sync::Mutex::new(Vec::new());
        static SESSION: SessionLease<Lease> = SessionLease::new();

        struct Lease(u8);

        impl Drop for Lease {
            fn drop(&mut self) {
                // `try_lock`: a drop under the session's lock is a defect to
                // record, not a hang.
                let held = match SESSION.0.try_lock() {
                    Ok(held) => held.as_ref().map(|lease| lease.0),
                    Err(_) => None,
                };
                DROPS.lock().unwrap_or_else(|error| error.into_inner()).push((self.0, held));
            }
        }

        fn held() -> Option<u8> {
            let session = SESSION.0.lock().unwrap_or_else(|error| error.into_inner());
            session.as_ref().map(|lease| lease.0)
        }

        fn drops() -> Vec<(u8, Option<u8>)> {
            DROPS.lock().unwrap_or_else(|error| error.into_inner()).clone()
        }

        fn apply(lease: u8, held_meanwhile: Option<u8>) {
            let mut command = std::process::Command::new("unused");
            apply_crate_memory_coordination_with(
                &mut command,
                &s(&["check"]),
                None,
                None,
                true,
                |_| {
                    assert_eq!(
                        held(),
                        held_meanwhile,
                        "the run holds its earlier lease while it takes the next"
                    );
                    Ok::<_, &str>(Lease(lease))
                },
                &SESSION,
            )
            .expect("an established daemon is leased");
        }

        apply(1, None);
        assert_eq!(held(), Some(1), "the session holds its lease after coordination returns");
        assert!(drops().is_empty(), "nothing ended the lease: {:?}", drops());

        apply(2, Some(1));
        assert_eq!(held(), Some(2));
        assert_eq!(
            drops(),
            [(1, Some(2))],
            "the earlier lease ends once, after its successor is stored"
        );
    }

    #[cfg(unix)]
    #[test]
    fn failed_unix_daemon_provisioning_exports_no_fallback_ledger() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-failure-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["build", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("/validated/toolchain/bin/targo");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "/tmp/inherited.tokens");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/tmp/inherited.sock");
        let error = apply_crate_memory_coordination_with(
            &mut command,
            &args,
            None,
            Some(std::ffi::OsStr::new("/tmp/inherited.tokens")),
            true,
            |_| Err::<(), _>("injected startup sentinel"),
            &SessionLease::new(),
        )
        .expect_err("identity/start failure must block Cargo launch");
        // T7b: a daemon that could not be established could not run the work:
        // exit 3, not a setup error.
        let ChildSetupError::CouldNotRun(error) = error else {
            panic!("a failed daemon start is could-not-run: {error:?}")
        };

        assert!(error.contains("refusing to launch a split-authority Cargo fan-out"));
        assert!(
            error.contains("injected startup sentinel"),
            "the exact startup cause must survive the Targo boundary: {error}"
        );
        assert!(
            error.contains(
                "executable `/validated/toolchain/bin/trustd` with arguments `--recover-after-crash --confirm-no-solvers"
            ),
            "recovery guidance must use the absolute same-sysroot trustd: {error}"
        );
        assert!(!error.contains("run `trustd --recover-after-crash"), "{error}");
        for authority in [TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV] {
            assert!(command.get_envs().any(|(name, value)| {
                name == std::ffi::OsStr::new(authority) && value.is_none()
            }));
        }
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(not(unix))]
    #[test]
    fn non_unix_verified_crate_mode_fails_without_exporting_an_authority() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-file-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["check", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "inherited.tokens");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "inherited.sock");
        let error = apply_crate_memory_coordination_with(
            &mut command,
            &args,
            None,
            None,
            false,
            |_| -> Result<(), &'static str> { panic!("non-Unix has no daemon transport") },
            &SessionLease::new(),
        )
        .expect_err("non-Unix must fail before uncoordinated worker fan-out");
        let ChildSetupError::Setup(error) = error else {
            panic!("an unsupported platform is a setup error: {error:?}")
        };
        assert!(error.contains("unsupported"));
        for authority in [TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV] {
            assert!(command.get_envs().any(|(name, value)| {
                name == std::ffi::OsStr::new(authority) && value.is_none()
            }));
        }
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn a_live_incumbent_daemon_is_waited_out_never_stopped() {
        // The remedy for a LIVE owner and a STALE socket are opposites, and the
        // live case is the one a toolchain promotion produces every time. If
        // this message ever tells an operator to stop the daemon again, it is
        // instructing them to abandon admitted solvers and record DIRTY.
        let args = s(&["check"]);
        // Absolute: the recovery suggestion refuses to name an ambient-PATH binary.
        let mut command = std::process::Command::new("/nonexistent/seal/bin/targo-trust");
        let error = apply_crate_memory_coordination_with(
            &mut command,
            &args,
            None,
            None,
            true,
            |sock| -> Result<(), String> { Err(format!("another trustd owns {}", sock.display())) },
            &SessionLease::new(),
        )
        .expect_err("a foreign live authority must refuse the fan-out");
        let ChildSetupError::CouldNotRun(error) = error else {
            panic!("a live incumbent daemon is could-not-run, re-run once it retires: {error:?}")
        };

        assert!(error.contains("WAIT for it to retire"), "{error}");
        assert!(
            error.contains(&trust_router::coordinator::IDLE_TIMEOUT.as_secs().to_string()),
            "the wait must name the actual idle timeout: {error}"
        );
        assert!(error.contains("Do NOT signal it"), "{error}");
        assert!(
            !error.contains("stop any incompatible live daemon"),
            "the old advice manufactures the wreckage the recovery sentence describes: {error}"
        );
        // The recovery attestation must stay scoped to an unclean exit.
        assert!(error.contains("ONLY for a daemon that already exited uncleanly"), "{error}");
    }

    /// T7b: an installation with no usable sibling daemon is a setup error
    /// (2), which re-running cannot change; a daemon that started and did not
    /// come up, or a spawn that failed for another reason, could not run (3).
    #[cfg(unix)]
    #[test]
    fn a_missing_sibling_daemon_is_setup_and_one_that_did_not_come_up_could_not_run() {
        use std::os::unix::process::ExitStatusExt as _;

        use trust_router::coordinator::EnsureDaemonError;

        let start = |error: EnsureDaemonError| {
            let mut command = std::process::Command::new("/validated/toolchain/bin/targo");
            apply_crate_memory_coordination_with(
                &mut command,
                &s(&["check"]),
                None,
                None,
                true,
                |_| Err::<(), _>(error),
                &SessionLease::new(),
            )
            .expect_err("a failed daemon start must block Cargo launch")
        };
        let executable = || "/validated/toolchain/bin/trustd".to_string();
        let io = std::io::Error::from;
        for installation in [
            EnsureDaemonError::SiblingUnavailable { executable: executable() },
            EnsureDaemonError::Spawn {
                executable: executable(),
                source: io(std::io::ErrorKind::NotFound),
            },
            EnsureDaemonError::Spawn {
                executable: executable(),
                source: io(std::io::ErrorKind::PermissionDenied),
            },
            EnsureDaemonError::ExecutableAuthority {
                executable: executable(),
                source: io(std::io::ErrorKind::InvalidData),
            },
        ] {
            let rendered = installation.to_string();
            let error = start(installation);
            let ChildSetupError::Setup(message) = &error else {
                panic!("an unusable installation is a setup error: {error:?}")
            };
            assert!(message.contains(&rendered), "{message}");
            assert_eq!(error.exit_code(), 2);
        }
        for daemon in [
            EnsureDaemonError::EarlyExit {
                executable: executable(),
                status: std::process::ExitStatus::from_raw(1 << 8),
                stderr: "bound to nothing".to_string(),
            },
            EnsureDaemonError::ReadinessTimeout {
                executable: executable(),
                timeout: std::time::Duration::from_secs(5),
            },
            EnsureDaemonError::Spawn {
                executable: executable(),
                source: io(std::io::ErrorKind::WouldBlock),
            },
        ] {
            let error = start(daemon);
            assert!(
                matches!(error, ChildSetupError::CouldNotRun(_)),
                "a daemon that did not come up could not run: {error:?}"
            );
            assert_eq!(error.exit_code(), crate::determinism_report::EXIT_COULD_NOT_RUN);
        }
    }

    #[cfg(unix)]
    #[test]
    fn child_signal_status_is_not_collapsed_to_generic_failure() {
        let status = std::process::Command::new("sh")
            .args(["-c", "kill -TERM $$"])
            .status()
            .expect("launch signal fixture");
        assert_eq!(child_signal_exit_code(&status), Some(128 + 15));
        assert_eq!(child_status_code(&status), 128 + 15);
    }

    #[test]
    fn target_dir_arg_handles_both_spellings_and_separator() {
        assert_eq!(
            cargo_target_dir_arg(&s(&["build", "--target-dir", "out/one"])),
            Some(std::path::PathBuf::from("out/one"))
        );
        assert_eq!(
            cargo_target_dir_arg(&s(&["build", "--target-dir=out/two"])),
            Some(std::path::PathBuf::from("out/two"))
        );
        assert_eq!(cargo_target_dir_arg(&s(&["build", "--", "--target-dir=target-code"])), None);
        assert_eq!(cargo_target_dir_arg(&s(&["build", "--target-dir="])), None);
        assert_eq!(
            cargo_target_dir(
                &s(&["test", "--target-dir", "out/phase-a"]),
                Some(std::path::Path::new("/metadata/default-target")),
            ),
            std::path::PathBuf::from("out/phase-a"),
            "the test execution manifest must bind Cargo's CLI target directory"
        );
    }

    #[test]
    fn verification_cache_root_tracks_the_selected_unit_not_the_calling_cwd() {
        let member =
            selection(vec![package("member", "path+file:///workspace/member#member@1.0.0")]);
        assert_eq!(
            verification_cache_target_dir(&s(&["check"]), Some(&member)),
            Some(PathBuf::from("/workspace/member/target")),
            "Cargo metadata's default workspace target must not absorb a lone member snapshot"
        );

        let workspace = selection(vec![
            package("member", "path+file:///workspace/member#member@1.0.0"),
            package("other", "path+file:///workspace/other#other@1.0.0"),
        ]);
        assert_eq!(
            verification_cache_target_dir(&s(&["check", "--workspace"]), Some(&workspace)),
            Some(PathBuf::from("/workspace/target")),
            "an aggregate selection retains Cargo's authenticated target directory"
        );

        assert_eq!(
            verification_cache_target_dir(
                &s(&["check", "--target-dir", "/explicit/target"]),
                Some(&member),
            ),
            Some(PathBuf::from("/explicit/target")),
            "an explicit Cargo target directory keeps CLI precedence"
        );

        let source_root = tempfile::tempdir().expect("single-file cache fixture");
        let source = source_root.path().join("demo.rs");
        std::fs::write(&source, "fn main() {}\n").expect("write single-file source");
        let canonical_source_root =
            std::fs::canonicalize(source_root.path()).expect("canonical single-file root");
        let single_file = [source.display().to_string()];
        assert_eq!(
            super::verification_cache_target_dir_with_env(&single_file, None, |_| None),
            Some(canonical_source_root.join("target")),
            "with no target directory named, the snapshot falls back beside the source"
        );
        for key in ["CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR"] {
            assert_eq!(
                super::verification_cache_target_dir_with_env(&single_file, None, |asked| {
                    (asked == key).then(|| "/named/target".into())
                }),
                Some(PathBuf::from("/named/target")),
                "a single-file check must not write beside the source when {key} names \
                 the target directory"
            );
        }
        assert_eq!(
            super::verification_cache_target_dir_with_env(&single_file, None, |_| {
                Some(std::ffi::OsString::new())
            }),
            Some(canonical_source_root.join("target")),
            "an empty target-directory variable names nothing"
        );
        assert_eq!(verification_cache_target_dir(&s(&["check"]), None), None);
    }

    #[test]
    fn canonical_selection_names_primary_packages_for_globs_workspaces_and_defaults() {
        let resolved = selection(vec![
            package("z-last", "path+file:///workspace/z#z-last@1.0.0"),
            package("a-first", "path+file:///workspace/a#a-first@1.0.0"),
            package("a-first", "registry+https://example.invalid#a-first@2.0.0"),
        ]);
        assert_eq!(
            selected_package_names_from_selection(&resolved),
            Some("a-first,z-last".to_string())
        );
    }

    #[test]
    fn verification_sessions_are_unique_and_injected_into_the_lane() {
        let first = VerificationSession::create().expect("create first session");
        let second = VerificationSession::create().expect("create second session");
        assert_ne!(first.id, second.id);
        for id in [&first.id, &second.id] {
            assert_eq!(id.len(), 64, "session ID must carry 256 random bits");
            assert!(
                id.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
                "session ID must use canonical lowercase hexadecimal: {id}"
            );
            assert!(
                !id.contains("trust-verify-session") && !id.contains(std::path::MAIN_SEPARATOR),
                "session ID must be an in-memory nonce, not a tempfile-derived path/name"
            );
        }
        assert_ne!(first.artifact_root(), second.artifact_root());
        assert!(first.artifact_root().is_dir());
        assert!(second.artifact_root().is_dir());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            assert_eq!(
                std::fs::metadata(first.artifact_root())
                    .expect("artifact root metadata")
                    .permissions()
                    .mode()
                    & 0o777,
                0o700
            );
        }

        let first_controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &first.id,
            proof_artifact_root: first.artifact_root(),
            spec_emit_dir: None,
        };
        let mut first_lane = Vec::new();
        append_verification_control_args(&mut first_lane, &first_controls)
            .expect("first lane controls");
        let plain = first_lane.join(" ");
        assert!(plain.contains(&format!("-Z trust-verify-session={}", first.id)));
        assert!(plain.contains(&format!(
            "-Z trust-proof-artifact-root={}",
            first.artifact_root().display()
        )));
        assert!(!plain.contains("trust-compiler-cache"));
        // Determinism plan §3.2a/§3.6: the built-in backstop's derived clocks
        // are exactly the clocks targo always passed, and the one effort
        // count always reaches the compiler, so the report's budget profile
        // is what it ran. The step budget is a seal constant: never passed.
        assert!(plain.contains("-Z trust-verify-timeout-ms=5000"));
        assert!(plain.contains("-Z trust-verify-function-budget-ms=120000"));
        assert!(plain.contains(&format!(
            "-Z trust-verify-effort={}",
            trust_types::determinism::EffortScale::BUILTIN.conflicts_per_node
        )));
        assert!(!plain.contains("trust-verify-function-budget-steps"));
        assert!(!plain.contains("trust-policy="));
        let mut raw_args = Vec::new();
        append_verification_control_args(&mut raw_args, &first_controls)
            .expect("raw rustc controls");
        assert!(raw_args.windows(2).any(|pair| {
            pair[0] == "-Z"
                && pair[1]
                    == format!("trust-proof-artifact-root={}", first.artifact_root().display())
        }));

        let slower = trust_types::determinism::BudgetProfile::new(
            trust_types::determinism::EffortScale { conflicts_per_node: 3 },
            trust_types::determinism::Backstop { per_mille: 1400 },
            0,
        );
        let second_controls = VerificationControls {
            policy: TrustPolicySelection::MemorySafe,
            budget: &slower,
            hardened_profile: Some("unix_hardened"),
            verification_session: &second.id,
            proof_artifact_root: second.artifact_root(),
            spec_emit_dir: None,
        };
        let mut second_lane = s(&["-C", "opt-level=2"]);
        append_verification_control_args(&mut second_lane, &second_controls)
            .expect("second lane controls");
        let encoded = encode_lane_rustflags(&second_lane).expect("encode the second lane");
        assert!(encoded.contains(&format!("\x1f-Z\x1ftrust-verify-session={}", second.id)));
        assert!(encoded.contains(&format!(
            "\x1f-Z\x1ftrust-proof-artifact-root={}",
            second.artifact_root().display()
        )));
        assert!(encoded.contains("\x1f-Z\x1ftrust-policy=memory-safe"));
        assert!(!encoded.contains("\x1f-Z\x1ftrust-policy=advisory"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-profile=unix_hardened"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-function-budget-ms=168000"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-timeout-ms=7000"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-effort=3"));
    }

    #[test]
    fn strict_lowering_policy_survives_cargo_environment_assembly_without_activation() {
        let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Certify,
            budget: &BUILTIN_BUDGET,
            hardened_profile: Some("unix_hardened"),
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
            spec_emit_dir: None,
        };
        // T7a: the Cargo-configuration route a tightening takes to the compile.
        let requirements = strictest_project_requirements();
        for encoded in [false, true] {
            let _plain = RustflagsEnvGuard::unset("RUSTFLAGS");
            let _encoded = if encoded {
                RustflagsEnvGuard::set("CARGO_ENCODED_RUSTFLAGS", "-C\x1fopt-level=2")
            } else {
                RustflagsEnvGuard::unset("CARGO_ENCODED_RUSTFLAGS")
            };
            let mut command = std::process::Command::new("unused");
            apply_lane_flags_env(LaneFlagsInput {
                cmd: &mut command,
                config: &TrustConfig::default(),
                selected_codegen_backend: Some("llvm"),
                supports_json_transport: true,
                strict_artifact_policy: true,
                allow_l0_gaps: false,
                controls: &controls,
                requirements: &requirements,
                cargo_args: &[],
            })
            .expect("assemble strict policy without spawning Cargo");
            let lane = exported_lane(&command);
            // The caller's representation is the caller's: the lane never
            // rewrites it, in either form.
            assert!(!sets_or_removes(&command, "CARGO_ENCODED_RUSTFLAGS"));
            assert!(!sets_or_removes(&command, "RUSTFLAGS"));
            let flags = &lane;
            let arguments = lane.iter().map(String::as_str).collect::<Vec<_>>();
            for option in [
                "trust-ir-lower=strict".to_string(),
                "trust-policy=certify".to_string(),
                "trust-verify-level=2".to_string(),
                "trust-verify-profile=unix_hardened".to_string(),
                "trust-verify-include-dependencies=yes".to_string(),
                format!("trust-verify-session={}", session.id),
                format!("trust-proof-artifact-root={}", session.artifact_root().display()),
            ] {
                assert_eq!(
                    arguments
                        .windows(2)
                        .filter(|pair| pair[0] == "-Z" && pair[1] == option)
                        .count(),
                    1,
                    "expected exactly one {option}: {flags:?}"
                );
            }
            assert!(!carries_verification_activation_option(&lane), "{flags:?}");
            // T7a: the adopted requirements are merged last.
            assert_eq!(
                &lane[lane.len() - 2..],
                ["-Z", "trust-ir-lower=strict"],
                "the requirements must come last: {lane:?}"
            );
        }
    }

    #[test]
    fn verification_session_deletes_its_private_artifact_root_on_drop() {
        let artifact_root = {
            let session = VerificationSession::create().expect("create session");
            let artifact_root = session.artifact_root().to_path_buf();
            std::fs::write(artifact_root.join("sentinel"), b"private proof bytes")
                .expect("write private artifact fixture");
            artifact_root
        };
        assert!(
            !artifact_root.exists(),
            "private proof artifact root survived its verification session: {}",
            artifact_root.display()
        );
    }

    #[test]
    fn verification_session_keeps_completed_mathematics_from_an_abandoned_run() {
        use trust_certify::proof_artifacts::{ProofArtifactStore, certify_vc_with_artifacts};
        use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

        // Use a private directory under this checkout: STORE-1 deliberately
        // refuses a cache below the world-writable system temporary directory.
        let workspace = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
        let store = || ProofArtifactStore::open(workspace.path()).unwrap();
        let x = || Formula::Var("x".into(), Sort::Int);
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "session proof hint".into() },
            function: "session_proof_hint".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
            ]),
            contract_metadata: None,
            obligation: None,
        };
        {
            let mut abandoned = VerificationSession::create().unwrap();
            let shared = store();
            shared.prepare_session(abandoned.artifact_root()).unwrap();
            abandoned.proof_store = Some(shared);
            assert!(certify_vc_with_artifacts(&vc, abandoned.artifact_root()).is_some());
            // Only the completed mathematics survives. No program verdict is
            // published when this run is abandoned.
        }
        let mut completed = VerificationSession::create().unwrap();
        store().prepare_session(completed.artifact_root()).unwrap();
        assert!(
            std::fs::read_dir(completed.artifact_root().join("kernel-proof-artifacts-v2/incoming"))
                .unwrap()
                .next()
                .is_none(),
            "opening a run must not snapshot unrelated shared proof hints",
        );
        completed.proof_store = Some(store());
        assert!(certify_vc_with_artifacts(&vc, completed.artifact_root()).is_some());
        completed.publish_proof_hints();
        drop(completed);
        let next = VerificationSession::create().unwrap();
        store().prepare_session(next.artifact_root()).unwrap();
        let proof = certify_vc_with_artifacts(&vc, next.artifact_root()).unwrap();
        assert!(trust_certify::reference_certificate_for(&proof).is_some());
    }

    #[test]
    fn proof_artifact_roots_with_whitespace_travel_in_one_lane_argument() {
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &session.id,
            proof_artifact_root: std::path::Path::new("/tmp/proof artifacts/run"),
            spec_emit_dir: None,
        };
        let lane = verified_lane_flags(
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &ProjectRequirementFlags::default(),
        )
        .expect("assemble a root-bearing lane");
        assert!(lane.iter().any(|arg| arg == "trust-proof-artifact-root=/tmp/proof artifacts/run"));
        let encoded = encode_lane_rustflags(&lane).expect("encode the lane");
        assert!(encoded.contains("\x1ftrust-proof-artifact-root=/tmp/proof artifacts/run"));
    }

    #[test]
    fn proof_artifact_root_rejects_the_encoded_rustflags_delimiter() {
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            budget: &BUILTIN_BUDGET,
            hardened_profile: None,
            verification_session: &session.id,
            proof_artifact_root: std::path::Path::new("/tmp/proof\u{1f}artifacts"),
            spec_emit_dir: None,
        };
        let error = match append_verification_control_args(&mut Vec::new(), &controls) {
            Err(error) => error,
            Ok(()) => panic!("the encoded-rustflags delimiter cannot be represented in one flag"),
        };
        assert!(error.contains("U+001F"), "{error}");
    }

    #[test]
    fn ephemeral_single_file_output_is_removed_with_its_guard() {
        let output = temp_single_file_output_path(&["example.rs".to_string()]);
        let directory = output.parent().expect("generated output parent").to_path_buf();
        let args = ["-o".to_string(), output.display().to_string()];

        let guard = prepare_ephemeral_single_file_output(&args, true)
            .expect("prepare output")
            .expect("enabled output guard");
        std::fs::write(&output, b"artifact").expect("write fake compiler artifact");
        assert!(directory.is_dir());
        drop(guard);
        assert!(!directory.exists());
    }
}

#[cfg(test)]
mod evidence_bundle_exit_tests {
    use super::{GateLane, closing_exit_disclosures, evidence_bundle_exit_override};
    use crate::report::EvidenceBundleStatus;

    fn incomplete() -> EvidenceBundleStatus {
        let mut status = EvidenceBundleStatus::empty(0);
        status.complete = false;
        status.omitted_artifacts = 1;
        status
    }

    /// Blocker 4: only the explicit advisory ramp exits per its verdict over
    /// an incomplete bundle. Every evidence-demanding run keeps exit 2.
    #[test]
    fn incomplete_bundle_keeps_exit_2_unless_the_advisory_lane_asked_for_no_evidence() {
        let incomplete = incomplete();
        let complete = EvidenceBundleStatus::empty(0);
        for lane in [GateLane::Strict, GateLane::Certify, GateLane::MemorySafe] {
            assert_eq!(evidence_bundle_exit_override(lane, false, Some(&incomplete)), Some(2));
            assert_eq!(evidence_bundle_exit_override(lane, true, Some(&incomplete)), Some(2));
            assert_eq!(evidence_bundle_exit_override(lane, false, Some(&complete)), None);
            assert_eq!(evidence_bundle_exit_override(lane, false, None), None);
        }
        assert_eq!(
            evidence_bundle_exit_override(GateLane::Advisory, false, Some(&incomplete)),
            None
        );
        assert_eq!(
            evidence_bundle_exit_override(GateLane::Advisory, true, Some(&incomplete)),
            Some(2),
            "--unsafe-memory asks for evidence even on the advisory lane"
        );
        assert_eq!(evidence_bundle_exit_override(GateLane::Advisory, true, Some(&complete)), None);
    }

    /// Review finding (2026-10-01): the incomplete-bundle override returned
    /// before the missing-trust-json diagnostic was printed, hiding the more
    /// fundamental failure.
    #[test]
    fn missing_trust_json_diagnostic_survives_the_incomplete_bundle_override() {
        use std::process::ExitCode;
        let incomplete = incomplete();
        let (lines, exit) = closing_exit_disclosures(
            GateLane::Strict,
            false,
            Some(&incomplete),
            Some("no trust-json was produced"),
            ExitCode::from(1),
        );
        assert_eq!(exit, Some(ExitCode::from(2)));
        assert_eq!(lines.len(), 2, "{lines:?}");
        assert_eq!(lines[0], "targo trust: error: no trust-json was produced");
        assert!(lines[1].contains("evidence bundle is incomplete"), "{lines:?}");
        assert!(lines[1].contains("strict lane"), "{lines:?}");

        // Without the override, the diagnostic still closes the run on its own exit.
        let (lines, exit) = closing_exit_disclosures(
            GateLane::Advisory,
            false,
            Some(&incomplete),
            Some("no trust-json was produced"),
            ExitCode::from(1),
        );
        assert_eq!(exit, Some(ExitCode::from(1)));
        assert_eq!(lines, vec!["targo trust: error: no trust-json was produced".to_string()]);

        // Neither: nothing printed, fall through.
        let (lines, exit) =
            closing_exit_disclosures(GateLane::Strict, false, None, None, ExitCode::from(0));
        assert!(lines.is_empty());
        assert_eq!(exit, None);

        // The lane is named the way the CLI spells it.
        let (lines, _) = closing_exit_disclosures(
            GateLane::MemorySafe,
            false,
            Some(&incomplete),
            None,
            ExitCode::from(0),
        );
        assert!(lines[0].contains("memory-safe lane"), "{lines:?}");
    }
}

#[cfg(test)]
mod run_exit_tests {
    use trust_types::determinism::UnitOutcome;

    use super::{RunExit, RunExitFacts, tests_failed};

    /// A concluded strict run with one row: passed unless told otherwise.
    fn facts() -> RunExitFacts {
        RunExitFacts {
            report_success: true,
            compiler_exit: 0,
            verification_concluded: true,
            fail_closed_rows_observed: false,
            every_unit_concluded: true,
            rows_fail_the_lane: false,
            tests_failed: false,
            configuration_gate_failed: false,
            refuted: false,
            outcome: UnitOutcome::Measured,
        }
    }

    /// A strict-lane unknown: trustc's fail-closed error makes Cargo exit 101
    /// in a session where every unit concluded, and the rows account for it.
    fn strict_unproved() -> RunExitFacts {
        RunExitFacts {
            report_success: false,
            compiler_exit: 101,
            fail_closed_rows_observed: true,
            rows_fail_the_lane: true,
            ..facts()
        }
    }

    /// The pre-T7b mapping of a measured run is unchanged: pass 0, verdict 1,
    /// otherwise the compiler's own status.
    #[test]
    fn a_measured_run_exits_as_before() {
        assert_eq!(RunExit::decide(facts()), RunExit::Passed);
        assert_eq!(RunExit::Passed.code(), 0);

        assert_eq!(RunExit::decide(strict_unproved()), RunExit::Verdict);
        assert_eq!(RunExit::Verdict.code(), 1);

        // A concluded run that failed for no verification reason, and a session
        // that never concluded, keep the compiler's own status.
        let compile_error = RunExitFacts { report_success: false, compiler_exit: 101, ..facts() };
        assert_eq!(RunExit::decide(compile_error), RunExit::Compiler(101));
        let ice = RunExitFacts {
            report_success: false,
            compiler_exit: 101,
            verification_concluded: false,
            every_unit_concluded: false,
            ..facts()
        };
        assert_eq!(RunExit::decide(ice), RunExit::Compiler(101));
        let no_status = RunExitFacts { report_success: false, ..facts() };
        assert_eq!(RunExit::decide(no_status), RunExit::Verdict);
    }

    /// T7b: rows that are no measurement exit 3 when they alone failed the
    /// run, whatever the lane would have said of them: a pass (the advisory
    /// ramp over an unknown) and an unproved verdict (the strict lane) alike,
    /// for both outcomes that are not `measured`.
    #[test]
    fn rows_that_are_no_measurement_could_not_run() {
        for outcome in [UnitOutcome::NotReproducible, UnitOutcome::CouldNotRun] {
            let passed = RunExitFacts { outcome, ..facts() };
            assert_eq!(RunExit::decide(passed), RunExit::CouldNotRun, "{outcome}");
            let unproved = RunExitFacts { outcome, ..strict_unproved() };
            assert_eq!(RunExit::decide(unproved), RunExit::CouldNotRun, "{outcome}");
            // An incomplete session with no compiler status of its own is no
            // measurement either.
            let incomplete = RunExitFacts {
                report_success: false,
                verification_concluded: false,
                every_unit_concluded: false,
                outcome,
                ..facts()
            };
            assert_eq!(RunExit::decide(incomplete), RunExit::CouldNotRun, "{outcome}");
        }
        assert_eq!(RunExit::CouldNotRun.code(), 3);
        assert_eq!(RunExit::CouldNotRun.code(), crate::baseline::EXIT_NOT_MEASURED);
    }

    /// A refutation is a verdict even in a run that is no measurement, as a
    /// LOST proof outranks NOT MEASURED in `diff --baseline`; and a session
    /// that died keeps the compiler's own status (an ICE after a proved
    /// prefix) whatever its rows' outcome.
    #[test]
    fn a_refutation_and_a_dead_compiler_outrank_the_missing_measurement() {
        let refuted = RunExitFacts {
            report_success: false,
            fail_closed_rows_observed: true,
            rows_fail_the_lane: true,
            refuted: true,
            outcome: UnitOutcome::NotReproducible,
            ..facts()
        };
        assert_eq!(RunExit::decide(refuted), RunExit::Verdict);
        let refuted_and_refused = RunExitFacts { outcome: UnitOutcome::CouldNotRun, ..refuted };
        assert_eq!(RunExit::decide(refuted_and_refused), RunExit::Verdict);

        let ice = RunExitFacts {
            report_success: false,
            compiler_exit: 101,
            verification_concluded: false,
            every_unit_concluded: false,
            outcome: UnitOutcome::NotReproducible,
            ..facts()
        };
        assert_eq!(RunExit::decide(ice), RunExit::Compiler(101));
    }

    /// A failure the rows do not account for is no question of measurement:
    /// re-running cannot change it, so it never exits 3, however the rows were
    /// decided. Each case maps as a measured run with the same failure does.
    #[test]
    fn a_failure_the_rows_do_not_account_for_never_could_not_run() {
        for outcome in [UnitOutcome::Measured, UnitOutcome::NotReproducible] {
            // `targo trust test`: the tests ran (phase A passed) and failed.
            // Their Cargo invocation's status passes through, even beside
            // runtime-checked rows the lane admits.
            let failing_test = RunExitFacts {
                report_success: false,
                compiler_exit: 101,
                fail_closed_rows_observed: true,
                tests_failed: true,
                outcome,
                ..facts()
            };
            assert_eq!(RunExit::decide(failing_test), RunExit::Compiler(101), "{outcome}");

            // A workspace whose concluded units' rows fail the lane while
            // another declared unit never concluded (a compile error): the
            // rows cannot account for that unit, so the run maps as before —
            // 1 over the non-proved rows.
            let compile_error_beside_unproved =
                RunExitFacts { every_unit_concluded: false, outcome, ..strict_unproved() };
            assert_eq!(
                RunExit::decide(compile_error_beside_unproved),
                RunExit::Verdict,
                "{outcome}"
            );
            // The same beside rows that all proved: the compiler's own status.
            let compile_error_beside_proved = RunExitFacts {
                report_success: false,
                compiler_exit: 101,
                every_unit_concluded: false,
                outcome,
                ..facts()
            };
            assert_eq!(
                RunExit::decide(compile_error_beside_proved),
                RunExit::Compiler(101),
                "{outcome}"
            );

            // The advisory ramp: its unknowns pass the lane, so trustc fails
            // nothing on them and they cannot account for a nonzero exit.
            let advisory_compile_error = RunExitFacts {
                report_success: false,
                compiler_exit: 101,
                fail_closed_rows_observed: true,
                rows_fail_the_lane: false,
                outcome,
                ..facts()
            };
            assert_eq!(RunExit::decide(advisory_compile_error), RunExit::Verdict, "{outcome}");
        }
    }

    /// The hardened proof-evidence gate and an active Unit excluded outside
    /// the dependency-TCB ledger are configuration and evidence, which a
    /// re-run cannot change: they outrank the missing measurement.
    #[test]
    fn a_gate_a_rerun_cannot_change_outranks_the_missing_measurement() {
        for outcome in [UnitOutcome::NotReproducible, UnitOutcome::CouldNotRun] {
            let gate = RunExitFacts {
                report_success: false,
                configuration_gate_failed: true,
                outcome,
                ..facts()
            };
            assert_eq!(RunExit::decide(gate), RunExit::Verdict, "{outcome}");
            let gate_and_unproved =
                RunExitFacts { configuration_gate_failed: true, outcome, ..strict_unproved() };
            assert_eq!(RunExit::decide(gate_and_unproved), RunExit::Verdict, "{outcome}");
        }
    }

    /// `check --rewrite` and `loop`: a converged loop passes only over a
    /// measurement; over rows that are no measurement it could not run (3);
    /// a loop that did not converge exits 1 whatever its rows were.
    #[test]
    fn the_rewrite_loop_passes_only_over_a_measurement() {
        use std::process::ExitCode;

        use super::rewrite_loop_exit;
        assert_eq!(rewrite_loop_exit(true, UnitOutcome::Measured), ExitCode::SUCCESS);
        for outcome in [UnitOutcome::NotReproducible, UnitOutcome::CouldNotRun] {
            assert_eq!(rewrite_loop_exit(true, outcome), ExitCode::from(3), "{outcome}");
            assert_eq!(rewrite_loop_exit(false, outcome), ExitCode::FAILURE, "{outcome}");
        }
        assert_eq!(rewrite_loop_exit(false, UnitOutcome::Measured), ExitCode::FAILURE);
    }

    /// Only an execution phase that reached Cargo's exit with a nonzero status
    /// is a failing test: a compile-only run, a blocked phase and a passing
    /// one are not.
    #[test]
    fn a_failing_test_is_an_execution_phase_that_exited_nonzero() {
        use crate::report::{
            CertifiedTestExecutionCompletionScope, CertifiedTestExecutionPhaseState,
            CertifiedTestExecutionReport,
        };
        let execution = |phase_b_exit| CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit,
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        };
        assert!(tests_failed(Some(&execution(Some(101)))));
        assert!(!tests_failed(Some(&execution(Some(0)))));
        assert!(!tests_failed(Some(&execution(None))));
        assert!(!tests_failed(None));
    }
}

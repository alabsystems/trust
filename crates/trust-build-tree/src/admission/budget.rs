//! Workload sizing DATA from fresh native observations and, when supplied, the
//! SAME original fixed claim. No policy result admits or launches any work.
//! This module opens no capacity pool, namespace, ticket or ownership record.

use std::io;
use std::num::{NonZeroU32, NonZeroU64};

use serde_derive::Serialize;

use super::InheritedFixedClaim;

const GIB: u64 = 1024 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Workload {
    RustcBuild,
    UiTest,
    CratesTest,
    FastLane,
}
impl Workload {
    pub fn parse(value: &str) -> io::Result<Self> {
        match value {
            "rustc-build" => Ok(Self::RustcBuild),
            "ui-test" => Ok(Self::UiTest),
            "crates-test" => Ok(Self::CratesTest),
            "fast-lane" => Ok(Self::FastLane),
            _ => Err(super::invalid("unknown native workload budget")),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::RustcBuild => "rustc-build",
            Self::UiTest => "ui-test",
            Self::CratesTest => "crates-test",
            Self::FastLane => "fast-lane",
        }
    }
    fn memory(self) -> (u64, u64) {
        // Workload properties carried from the existing host-budget policy,
        // rather than machine-specific CPU or physical-memory constants.
        match self {
            Self::RustcBuild => (5 * GIB / 2, 3 * GIB / 2),
            Self::UiTest => (GIB, GIB / 2),
            Self::CratesTest => (16 * GIB, 2 * GIB),
            Self::FastLane => (GIB / 2, GIB / 4),
        }
    }
}

/// Caller limits may reduce policy suggestions. These are never resource
/// claims; the optional original claim is authenticated independently below.
pub struct Request {
    pub workload: Workload,
    pub maximum_jobs: Option<NonZeroU32>,
    pub want_bytes: Option<NonZeroU64>,
    pub floor_bytes: Option<NonZeroU64>,
}
impl Request {
    pub fn new(workload: Workload) -> Self {
        Self { workload, maximum_jobs: None, want_bytes: None, floor_bytes: None }
    }
}

#[derive(Debug, Serialize)]
pub struct Host {
    pub platform: &'static str,
    pub cpus: u32,
    pub physical_memory_bytes: u64,
    pub available_memory_bytes: u64,
    pub available_memory_source: &'static str,
    pub load_one: Option<f64>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CpuScope {
    UnmanagedPolicy,
    OriginalFixed { ceiling: u32 },
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    FitsMeasuredMemory,
    BelowMemoryFloor,
}

#[derive(Debug, Serialize)]
pub struct Plan {
    pub workload: Workload,
    pub outcome: Outcome,
    pub jobs: u32,
    pub cap_bytes: u64,
    pub want_bytes: u64,
    pub floor_bytes: u64,
    pub reserve_bytes: u64,
    pub room_bytes: u64,
    pub cpu_bound: u32,
    pub memory_bound: u64,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Overlap {
    OriginalFixedRequiresSerial,
    BelowMemoryFloor,
    BelowFullCpuMemoryWant,
    FitsMeasuredMemory,
}

#[derive(Debug, Serialize)]
pub struct GovernorFloors {
    pub critical_gib: u64,
    pub resume_gib: u64,
}

#[derive(Debug, Serialize)]
pub struct Report {
    pub protocol: &'static str,
    pub authority: &'static str,
    pub host: Host,
    pub cpu_scope: CpuScope,
    pub plan: Plan,
    pub overlap: Option<Overlap>,
    pub governor: GovernorFloors,
}

/// A fresh policy observation. Existing fixed custody is checked on BOTH
/// sides of all native observation/calculation; no environment integer selects
/// that owner. Unavailable readings return an error, never a zero/free claim.
pub fn current(request: &Request, original: Option<&InheritedFixedClaim>) -> io::Result<Report> {
    let ceiling = original.map(InheritedFixedClaim::budget).transpose()?;
    let host = native::measure()?;
    let report = observed(host, request, ceiling);
    if original.map(InheritedFixedClaim::budget).transpose()? != ceiling {
        return Err(super::invalid("original native budget changed during observation"));
    }
    Ok(report)
}

fn observed(host: Host, request: &Request, ceiling: Option<NonZeroU32>) -> Report {
    let defaults = request.workload.memory();
    let want = request.want_bytes.map_or(defaults.0, NonZeroU64::get);
    let floor = request.floor_bytes.map_or(defaults.1, NonZeroU64::get).min(want);
    let reserve = GIB.max(host.physical_memory_bytes / 8);
    let room = host.available_memory_bytes.saturating_sub(reserve);
    let cpu_bound = host.cpus.min(ceiling.map_or(u32::MAX, NonZeroU32::get));
    let memory_bound = room / want;
    let fits = room >= floor;
    let jobs = if fits {
        u64::from(cpu_bound)
            .min(memory_bound)
            .max(1)
            .min(u64::from(request.maximum_jobs.map_or(u32::MAX, NonZeroU32::get))) as u32
    } else {
        0
    };
    let plan = Plan {
        workload: request.workload,
        outcome: if fits { Outcome::FitsMeasuredMemory } else { Outcome::BelowMemoryFloor },
        jobs,
        cap_bytes: if fits { room / u64::from(jobs) } else { 0 },
        want_bytes: want,
        floor_bytes: floor,
        reserve_bytes: reserve,
        room_bytes: room,
        cpu_bound,
        memory_bound,
    };
    // Overlap is meaningful only for the compiler-build policy. An actual
    // original fixed share is always kept serial; it cannot be spent twice.
    let overlap = if ceiling.is_some() {
        Some(Overlap::OriginalFixedRequiresSerial)
    } else if request.workload != Workload::RustcBuild {
        // This request did not supply the compiler policy/overrides. Do not
        // invent that independent plan from another workload's observations.
        None
    } else if room < floor {
        Some(Overlap::BelowMemoryFloor)
    } else if u64::from(host.cpus).checked_mul(want).is_some_and(|need| room >= need) {
        Some(Overlap::FitsMeasuredMemory)
    } else {
        Some(Overlap::BelowFullCpuMemoryWant)
    };
    let critical = GIB.max(host.physical_memory_bytes / 16);
    let governor = GovernorFloors {
        critical_gib: critical.div_ceil(GIB),
        resume_gib: (2 * critical).div_ceil(GIB),
    };
    Report {
        protocol: "native-host-budget-v1",
        authority: "policy_data_only_no_admission",
        host,
        cpu_scope: ceiling.map_or(CpuScope::UnmanagedPolicy, |ceiling| CpuScope::OriginalFixed {
            ceiling: ceiling.get(),
        }),
        plan,
        overlap,
        governor,
    }
}

mod native;
#[cfg(test)]
mod tests;

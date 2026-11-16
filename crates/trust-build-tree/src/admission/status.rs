//! Read-only observations of the original account's machine coordination.
//!
//! Rows are sampled sequentially, not an atomic machine-wide capacity claim.
//! Shared lock probes and reported owner data grant no admission or control.
//! Missing, busy, malformed and unknown states never mean available capacity.

use trust_build_cpu::{ExternalDebt, LegacyRetirement, Pool, RetainedSlotState, SlotState};

use super::*;

mod legacy;

/// One explicitly graded observation, with no resource or recovery authority.
#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum Observation<T> {
    Observed { value: T },
    Absent,
    Busy,
    Unavailable { message: String, raw_os_error: Option<i32> },
}
impl<T> Observation<T> {
    fn observed(value: T) -> Self {
        Self::Observed { value }
    }
    fn error(error: io::Error) -> Self {
        Self::Unavailable { message: error.to_string(), raw_os_error: error.raw_os_error() }
    }
    fn result(result: io::Result<T>) -> Self {
        match result {
            Ok(value) => Self::observed(value),
            Err(error) => Self::error(error),
        }
    }
}

/// Versioned diagnostic data. No constructor in this module returns an owner.
#[derive(Debug, Serialize)]
pub struct MachineStatus {
    pub protocol: &'static str,
    pub native_capacity_bytes: Vec<u8>,
    pub legacy_namespace_bytes: Vec<u8>,
    pub available_memory_bytes: Option<u64>,
    pub native: Observation<NativeStatus>,
    pub legacy: Observation<LegacyStatus>,
}

#[derive(Debug, Serialize)]
pub struct NativeStatus {
    pub slots: Vec<NativeSlot>,
    /// Absent means activation paths were actually absent, never zero debt.
    pub external: Observation<Vec<NativeSlot>>,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct NativeSlot {
    pub slot: u32,
    pub state: NativeSlotState,
    pub reported_pid: Option<u32>,
    pub reported_birth: Option<u64>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum NativeSlotState {
    SharedCompatible,
    Held,
    Retained,
}

#[derive(Debug, Serialize)]
pub struct LegacyStatus {
    pub slots: Vec<LeaseObservation>,
    /// This distinguishes an exclusive fence from a shared-compatible probe.
    /// It cannot certify that no shared participant exists.
    pub admission: LeaseObservation,
    pub queue: Observation<QueueStatus>,
    pub adopted: Observation<Vec<AdoptionObservation>>,
}

#[derive(Debug, Serialize)]
pub struct LeaseObservation {
    pub name_bytes: Vec<u8>,
    pub lock: Observation<LockState>,
    pub reported: Observation<ReportedOwner>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LockState {
    SharedCompatible,
    ExclusiveHeld,
}
/// Unauthenticated record data, separate from the actual lock observation.
#[derive(Debug, Serialize)]
pub struct ReportedOwner {
    pub pid: Option<u32>,
    pub cpu_mode: Option<String>,
    pub cpu_budget: Option<u32>,
    pub exclusive: Option<bool>,
    pub command: Option<String>,
    pub cwd: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct QueueStatus {
    /// Complete bounded population, including unlocked stale records.
    pub tickets: Vec<TicketObservation>,
}
#[derive(Debug, Serialize)]
pub struct TicketObservation {
    pub name_bytes: Vec<u8>,
    pub order: u128,
    pub lock: Observation<LockState>,
    pub requirements: Observation<RequirementObservation>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct RequirementObservation {
    pub worktree_bytes: Option<Vec<u8>>,
    pub slots: u32,
    pub needed: u32,
    pub exclusive: bool,
    pub minimum_memory_bytes: u64,
}
impl From<Requirements> for RequirementObservation {
    fn from(value: Requirements) -> Self {
        Self {
            worktree_bytes: value.worktree.map(|path| path.as_os_str().as_bytes().to_vec()),
            slots: value.slots,
            needed: value.needed,
            exclusive: value.exclusive,
            minimum_memory_bytes: value.minimum_memory_bytes,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct AdoptionObservation {
    pub name_bytes: Vec<u8>,
    pub record: Observation<AdoptedRecord>,
}
#[derive(Debug, Serialize)]
pub struct AdoptedRecord {
    pub reported_pid: u32,
    pub reported_birth: String,
    pub lease_paths_bytes: Vec<Vec<u8>>,
    /// Even GoneOrReused does not remove the record or release any debt.
    pub process: Observation<AdoptedProcess>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AdoptedProcess {
    SameBirth,
    GoneOrReused,
}

/// Observe only the account's existing canonical namespaces. No directory,
/// pool, registry, ticket or record is created, repaired, or retired.
pub fn current() -> io::Result<MachineStatus> {
    let namespace = resources::account_home()?.join(".cache/build-slot");
    if let Some(selected) = std::env::var_os("BUILD_SLOT_DIR").filter(|value| !value.is_empty()) {
        let selected = PathBuf::from(selected);
        if selected != namespace && fs::canonicalize(&selected)? != fs::canonicalize(&namespace)? {
            return Err(invalid("resource status observes only the canonical machine namespace"));
        }
    }
    let capacity = trust_build_cpu::capacity_dir()?;
    let retirement = LegacyRetirement::open_canonical().ok();
    Ok(snapshot(&namespace, &capacity, retirement.as_ref()))
}

/// Native status frontdoor shared by the actual Targo entry and unit actors.
/// Parse the closed spelling before selecting or opening any namespace.
pub fn command(args: &[std::ffi::OsString], output: &mut impl Write) -> io::Result<()> {
    let compact = match args {
        [] => false,
        [arg] if arg == "--json" => true,
        [arg] if arg == "--help" || arg == "-h" => {
            return writeln!(
                output,
                "Usage: targo --unverified resource status [--json]\n\nObserve the existing canonical machine namespace. JSON data only; no admission, cleanup or capacity grant. Default output is pretty JSON."
            );
        }
        _ => {
            return Err(invalid(
                "resource status accepts only --json or --help; no namespace or resource options",
            ));
        }
    };
    let status = current()?;
    if compact {
        serde_json::to_writer(&mut *output, &status).map_err(io::Error::other)?;
    } else {
        serde_json::to_writer_pretty(&mut *output, &status).map_err(io::Error::other)?;
    }
    writeln!(output)
}

fn snapshot(
    namespace: &Path,
    capacity: &Path,
    retirement: Option<&LegacyRetirement>,
) -> MachineStatus {
    let native = match Pool::open_existing(capacity) {
        Ok(None) => Observation::Absent,
        Err(error) => Observation::error(error),
        Ok(Some(pool)) => Observation::result(native_status(&pool, retirement)),
    };
    let minimum = match &native {
        Observation::Observed { value } => Some((value.slots.len() as u32 / 6).max(1)),
        _ => None,
    };
    MachineStatus {
        protocol: "native-resource-status-v1",
        native_capacity_bytes: capacity.as_os_str().as_bytes().to_vec(),
        legacy_namespace_bytes: namespace.as_os_str().as_bytes().to_vec(),
        available_memory_bytes: trust_build_cpu::available_memory(),
        native,
        legacy: legacy::snapshot(namespace, minimum),
    }
}

fn native_status(pool: &Pool, retirement: Option<&LegacyRetirement>) -> io::Result<NativeStatus> {
    let slots = native_slots(pool.snapshot()?);
    let external = match ExternalDebt::observe(pool, retirement) {
        Ok((_, None)) => Observation::Absent,
        Ok((_, Some(slots))) => Observation::observed(
            slots
                .into_iter()
                .map(|value| {
                    let (slot, state, owner) = match value {
                        RetainedSlotState::Available { slot } => {
                            (slot, NativeSlotState::SharedCompatible, None)
                        }
                        RetainedSlotState::Held { slot, reported_owner } => {
                            (slot, NativeSlotState::Held, reported_owner)
                        }
                        RetainedSlotState::Retained { slot, reported_owner } => {
                            (slot, NativeSlotState::Retained, Some(reported_owner))
                        }
                    };
                    NativeSlot {
                        slot,
                        state,
                        reported_pid: owner.map(|o| o.pid),
                        reported_birth: owner.and_then(|o| o.birth),
                    }
                })
                .collect(),
        ),
        Err(error) if error.kind() == io::ErrorKind::WouldBlock => Observation::Busy,
        Err(error) => Observation::error(error),
    };
    // Revalidate the same original manifest after observing the sidecar. The
    // rows remain sequential observations, not one admission transaction.
    pool.snapshot()?;
    Ok(NativeStatus { slots, external })
}

fn native_slots(slots: Vec<SlotState>) -> Vec<NativeSlot> {
    slots
        .into_iter()
        .map(|value| {
            let (slot, state, owner) = match value {
                SlotState::Available { slot } => (slot, NativeSlotState::SharedCompatible, None),
                SlotState::Held { slot, reported_owner } => {
                    (slot, NativeSlotState::Held, reported_owner)
                }
            };
            NativeSlot {
                slot,
                state,
                reported_pid: owner.map(|o| o.pid),
                reported_birth: owner.and_then(|o| o.birth),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests;

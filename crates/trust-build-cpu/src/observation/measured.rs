// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Typed native measurements, independent of GUI JSON or controller transport.
use super::*;

/// Unknown sensor states never become normal pressure by default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryPressure {
    /// No usable measurement; do not assume normal pressure.
    Unknown,
    /// No measured memory-pressure restriction.
    Normal,
    /// Reduce new admission under measured warning pressure.
    Warn,
    /// Pause new admission under critical pressure.
    Critical,
}
/// Native thermal feedback; critical pauses all fresh admissions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThermalPressure {
    /// No usable measurement; do not assume nominal temperature.
    Unknown,
    /// No measured thermal restriction.
    Nominal,
    /// Moderate measured thermal pressure.
    Fair,
    /// Strong measured thermal pressure.
    Serious,
    /// Pause new admission under critical thermal pressure.
    Critical,
}
/// Original sample timing is retained, including time spent in RPC/FD checks.
/// This is observation only; callers separately authenticate its native source.
pub struct Measurements {
    /// Monotonic receipt instant, never reset by cache reads.
    pub received: Instant,
    /// Source-reported age when the reply arrived.
    pub age: Duration,
    /// Interval over which busy CPU was measured.
    pub window: Duration,
    /// Measured machine CPU count.
    pub cpus: u32,
    /// Actually busy millicores, including native workers themselves.
    pub busy_millicores: Option<u64>,
    /// Raw measured available memory, not reserved entitlement.
    pub available_memory: Option<u64>,
    /// Measured memory pressure.
    pub pressure: MemoryPressure,
    /// Measured thermal pressure.
    pub thermal: ThermalPressure,
}
impl Observation {
    /// Convert an authenticated typed sample without fabricating JSON or
    /// freshness. Unknown essential sensors and invalid intervals refuse.
    pub fn from_measurements(sample: Measurements) -> io::Result<Self> {
        let busy =
            sample.busy_millicores.ok_or_else(|| invalid("native busy CPU is unavailable"))?;
        if sample.cpus == 0
            || sample.cpus > MAX_SLOTS
            || busy > u64::from(sample.cpus) * 1000
            || sample.age > MAX_AGE
            || sample.window.is_zero()
            || sample.window > MAX_AGE
        {
            return Err(invalid("native observation interval or CPU count is unavailable"));
        }
        let available_memory = sample
            .available_memory
            .ok_or_else(|| invalid("native available memory is unavailable"))?;
        let pressure_divisor = match sample.pressure {
            MemoryPressure::Normal => 1,
            MemoryPressure::Warn => 2,
            MemoryPressure::Critical => 0,
            MemoryPressure::Unknown => {
                return Err(invalid("native memory pressure is unavailable"));
            }
        };
        let thermal_divisor = match sample.thermal {
            ThermalPressure::Nominal => 1,
            ThermalPressure::Fair => 2,
            ThermalPressure::Serious => 4,
            ThermalPressure::Critical => 0,
            ThermalPressure::Unknown => {
                return Err(invalid("native thermal pressure is unavailable"));
            }
        };
        Ok(Self {
            received: sample.received,
            age: sample.age,
            cpus: sample.cpus,
            busy_millicores: busy,
            available_memory,
            pressure_divisor,
            thermal_divisor,
        })
    }
}

// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! An aterm observation can veto admission; it never grants a reservation.

use std::io;
use std::num::NonZeroU64;
use std::time::{Duration, Instant};

use serde_json::Value;

use crate::{MAX_SLOTS, invalid};

const MAX_BYTES: usize = 65_536;
const MAX_AGE: Duration = Duration::from_secs(3);

/// A typed, fresh `aterm ctl @self sys --json` overview.
///
/// Keep the local monotonic receipt age as well as the monitor's sample age.
/// A cache hit must not make an old host measurement fresh again.
#[derive(Clone, Debug)]
pub struct Observation {
    received: Instant,
    age: Duration,
    cpus: u32,
    busy_millicores: u64,
    available_memory: u64,
    pressure_divisor: u32,
    thermal_divisor: u32,
}

impl Observation {
    /// Parse the existing authenticated overview schema, refusing unknown
    /// numbers, warming/stale samples and unknown pressure/thermal states.
    /// The caller must obtain these bytes through its authenticated aterm
    /// control route; JSON shape alone authenticates no monitor or authority.
    pub fn from_aterm_sys(bytes: &[u8], received: Instant) -> io::Result<Self> {
        if bytes.len() > MAX_BYTES {
            return Err(invalid("aterm CPU observation exceeds its size bound"));
        }
        let value: Value = serde_json::from_slice(bytes)
            .map_err(|_| invalid("aterm CPU observation is not JSON"))?;
        if value["schema"].as_u64() != Some(1)
            || value["kind"].as_str() != Some("sys.overview")
            || value["as_of"]["state"].as_str() != Some("fresh")
        {
            return Err(invalid("aterm CPU observation is not a fresh version-one overview"));
        }
        let cpus = value["machine"]["cpus"]
            .as_u64()
            .filter(|&cpus| cpus > 0 && cpus <= u64::from(MAX_SLOTS))
            .ok_or_else(|| invalid("aterm CPU count is unavailable"))? as u32;
        let busy_millicores = value["global"]["cpu_mc"]
            .as_u64()
            .ok_or_else(|| invalid("aterm busy CPU measurement is unavailable"))?;
        let available_memory = value["global"]["mem_available_bytes"]
            .as_u64()
            .ok_or_else(|| invalid("aterm available memory measurement is unavailable"))?;
        if value["global"]["mem_available_basis"].as_str() != Some("free_plus_reclaimable_cache") {
            return Err(invalid("aterm available memory basis is unsupported"));
        }
        let age = Duration::from_millis(
            value["as_of"]["age_ms"]
                .as_u64()
                .ok_or_else(|| invalid("aterm sample age is unavailable"))?,
        );
        if age > MAX_AGE {
            return Err(invalid("aterm CPU observation is stale"));
        }
        if !value["as_of"]["window_ms"]
            .as_u64()
            .is_some_and(|window| window > 0 && window <= MAX_AGE.as_millis() as u64)
        {
            return Err(invalid("aterm CPU observation window is unavailable or too long"));
        }
        let pressure_divisor = match value["global"]["mem_pressure"].as_str() {
            Some("normal") => 1,
            Some("warn") => 2,
            Some("critical") => 0,
            _ => return Err(invalid("aterm memory pressure is unavailable")),
        };
        let thermal_divisor = match value["global"]["thermal"].as_str() {
            Some("nominal" | "none") => 1,
            Some("fair" | "light") => 2,
            Some("serious" | "heavy") => 4,
            Some("critical" | "severe") => 0,
            _ => return Err(invalid("aterm thermal measurement is unavailable")),
        };
        Ok(Self {
            received,
            age,
            cpus,
            busy_millicores,
            available_memory,
            pressure_divisor,
            thermal_divisor,
        })
    }

    /// Compute an advisory total lease ceiling for the next acquisition.
    ///
    /// `native_busy_millicores` is independently measured CPU of validated
    /// lease-owner processes over a compatible recent window, not a count of
    /// held leases. Subtracting it avoids throttling our own busy workers.
    /// Missing owner observations contribute no CPU, conservatively treating
    /// that activity as external. A held-but-idle lease is never counted busy.
    /// `claimable_memory` is the independent stricter host/ledger budget; the
    /// monitor's reclaimable cache estimate must never enlarge it.
    /// `per_worker` and `reserve` are the execution owner's memory policy,
    /// not a claim that arbitrary compiler work has a fixed memory cost.
    /// Critical, stale, missing stricter memory, or zero headroom yields zero.
    pub fn admission_limit(
        &self,
        now: Instant,
        native_busy_millicores: u64,
        claimable_memory: u64,
        per_worker: NonZeroU64,
        reserve: u64,
    ) -> u32 {
        let Some(local_age) = now.checked_duration_since(self.received) else { return 0 };
        if self.age.saturating_add(local_age) > MAX_AGE
            || self.pressure_divisor == 0
            || self.thermal_divisor == 0
        {
            return 0;
        }
        let external = self.busy_millicores.saturating_sub(native_busy_millicores);
        let cpu = (u64::from(self.cpus) * 1000).saturating_sub(external) / 1000;
        let memory =
            self.available_memory.min(claimable_memory).saturating_sub(reserve) / per_worker;
        (cpu.min(memory) / u64::from(self.pressure_divisor.max(self.thermal_divisor))) as u32
    }
}

#[cfg(test)]
mod tests;

mod measured;
pub use measured::{Measurements, MemoryPressure, ThermalPressure};

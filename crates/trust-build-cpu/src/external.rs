// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Observe the fixed part of build-slot's kernel-held reservations.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{self, Read};
use std::os::unix::fs::MetadataExt;
use std::path::Path;

use crate::{MAX_SLOTS, invalid};

/// Readiness observed while holding the ORIGINAL native manifest transaction.
/// These facts are not execution, SDK, memory or original GNU-credit grants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegacyFixedRoom {
    /// Another manifest transaction is active. No observation was made.
    Busy,
    /// A live external record is unknown or its full claim is inconsistent.
    UnknownExternal,
    /// Known fixed and native occupancy exceed the original machine width.
    OverCapacity {
        /// Actual native leases held at observation.
        native_held: u32,
        /// Full fixed reservations, counted once per original lease ID.
        external_reserved: u64,
        /// Width of the original native manifest.
        capacity: u32,
    },
    /// Known occupancy fits at observation. The caller must retain its already
    /// published original fixed locks, and all participants must honor the
    /// legacy fence/record protocol. This does not reserve new native leases.
    Fits {
        /// Actual native leases held at observation.
        native_held: u32,
        /// Full fixed reservations, counted once per original lease ID.
        external_reserved: u64,
        /// Width of the original native manifest.
        capacity: u32,
    },
}

enum Reservations {
    Known(u64),
    Unknown,
}

/// Count external fixed CPU reservations while the caller holds its native
/// pool's admission lock. This function never waits for an external holder.
/// Unlocked stale metadata counts zero; held unknown metadata vetoes the full
/// host. The lock, not the reported PID, establishes that a record is live.
#[cfg(test)]
fn reserved_cpus(directory: &Path, cpus: u32, slots: u32) -> io::Result<u32> {
    Ok(match reservations(directory, cpus, slots, None)? {
        Reservations::Known(known) => known.min(u64::from(cpus)) as u32,
        Reservations::Unknown => cpus,
    })
}

pub(super) fn observe_fixed(
    directory: &Path,
    cpus: u32,
    slots: u32,
    owned_exclusive_admission: Option<&File>,
    native_held: u32,
) -> io::Result<LegacyFixedRoom> {
    let Reservations::Known(external_reserved) =
        reservations(directory, cpus, slots, owned_exclusive_admission)?
    else {
        return Ok(LegacyFixedRoom::UnknownExternal);
    };
    Ok(if u64::from(native_held) + external_reserved > u64::from(cpus) {
        LegacyFixedRoom::OverCapacity { native_held, external_reserved, capacity: cpus }
    } else {
        LegacyFixedRoom::Fits { native_held, external_reserved, capacity: cpus }
    })
}

fn reservations(
    directory: &Path,
    cpus: u32,
    slots: u32,
    owned_exclusive_admission: Option<&File>,
) -> io::Result<Reservations> {
    if !directory.is_absolute() || cpus == 0 || slots == 0 || slots > MAX_SLOTS {
        return Err(invalid("invalid external CPU reservation namespace"));
    }
    let root = match crate::unix::open_parent(directory) {
        Ok(root) => root,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Reservations::Known(0)),
        Err(error) => return Err(error),
    };
    match open_record(&root, "admission.lock") {
        Ok(fence) if held(&fence)? => {
            if !owned_exclusive_admission
                .is_some_and(|original| same_original_fence(original, &fence).unwrap_or(false))
            {
                return Ok(Reservations::Unknown);
            }
        }
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    let mut seen = BTreeMap::new();
    let mut total = 0u64;
    let weight = cpus.div_ceil(slots);
    let mut count = 0;
    for entry in std::fs::read_dir(directory)? {
        let entry = entry?;
        count += 1;
        if count > MAX_SLOTS + 16 {
            return Err(invalid("too many external namespace entries"));
        }
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let Some(index) = name.strip_prefix("slot-") else { continue };
        if index.is_empty() || !index.bytes().all(|byte| byte.is_ascii_digit()) {
            continue;
        }
        let index: u32 = index.parse().map_err(|_| invalid("external slot index overflows"))?;
        let mut file = open_record(&root, name)?;
        if !held(&file)? {
            continue;
        }
        let mut bytes = Vec::new();
        Read::by_ref(&mut file).take(65_537).read_to_end(&mut bytes)?;
        if bytes.len() > 65_536 {
            return Ok(Reservations::Unknown);
        }
        let Ok(UniqueValue(row)) = serde_json::from_slice::<UniqueValue>(&bytes) else {
            return Ok(Reservations::Unknown);
        };
        let Some(row) = row.as_object() else { return Ok(Reservations::Unknown) };
        let Some(mode) = row.get("cpu_mode") else {
            if !row.get("pid").and_then(|n| n.as_u64()).is_some_and(|pid| pid > 0)
                || row.get("cmd").and_then(|s| s.as_str()).is_none()
                || !row
                    .get("cwd")
                    .and_then(|s| s.as_str())
                    .is_some_and(|cwd| Path::new(cwd).is_absolute())
                || !row
                    .get("started")
                    .and_then(|n| n.as_f64())
                    .is_some_and(|n| n.is_finite() && n >= 0.0)
            {
                return Ok(Reservations::Unknown);
            }
            total += u64::from(if index >= slots { cpus } else { weight });
            continue;
        };
        let mode = mode.as_str().unwrap_or("");
        let lease = row.get("lease_id").and_then(|id| id.as_str()).unwrap_or("");
        let budget = row.get("cpu_budget").and_then(|n| n.as_u64()).unwrap_or(0);
        let pool_slots = row.get("pool_slots").and_then(|n| n.as_u64()).unwrap_or(0);
        if !matches!(mode, "workers-v1" | "fixed-v1")
            || lease.len() != 32
            || !lease.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || budget == 0
            || budget > u64::from(cpus)
            || pool_slots == 0
            || pool_slots > u64::from(MAX_SLOTS)
            || u64::from(index) >= pool_slots
        {
            return Ok(Reservations::Unknown);
        }
        let identity = (mode.to_owned(), budget, pool_slots);
        if let Some(previous) = seen.get(lease) {
            if previous != &identity {
                return Ok(Reservations::Unknown);
            }
        } else {
            seen.insert(lease.to_owned(), identity);
            if mode == "fixed-v1" {
                total += budget;
            }
        }
    }
    let named = std::fs::symlink_metadata(directory)?;
    let original = root.metadata()?;
    if !named.is_dir() || named.dev() != original.dev() || named.ino() != original.ino() {
        return Err(invalid("external CPU reservation directory changed"));
    }
    Ok(Reservations::Known(total))
}

// serde_json::Value normally accepts duplicate keys by overwriting the earlier
// value. A held CPU record with contradictory budgets/identities is UNKNOWN.
// Preserve the normal JSON recursion limit and bounded record byte population.
struct UniqueValue(serde_json::Value);
impl<'de> serde::Deserialize<'de> for UniqueValue {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visitor;
        impl<'de> serde::de::Visitor<'de> for Visitor {
            type Value = UniqueValue;
            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("JSON with unique object keys")
            }
            fn visit_map<M: serde::de::MapAccess<'de>>(
                self,
                mut map: M,
            ) -> Result<Self::Value, M::Error> {
                let mut values = serde_json::Map::new();
                while let Some(key) = map.next_key::<String>()? {
                    if values.contains_key(&key) {
                        return Err(serde::de::Error::custom(
                            "duplicate external CPU record field",
                        ));
                    }
                    values.insert(key, map.next_value::<UniqueValue>()?.0);
                }
                Ok(UniqueValue(serde_json::Value::Object(values)))
            }
            fn visit_seq<S: serde::de::SeqAccess<'de>>(
                self,
                mut sequence: S,
            ) -> Result<Self::Value, S::Error> {
                let mut values = Vec::new();
                while let Some(value) = sequence.next_element::<UniqueValue>()? {
                    values.push(value.0);
                }
                Ok(UniqueValue(serde_json::Value::Array(values)))
            }
            fn visit_bool<E: serde::de::Error>(self, value: bool) -> Result<Self::Value, E> {
                Ok(UniqueValue(value.into()))
            }
            fn visit_i64<E: serde::de::Error>(self, value: i64) -> Result<Self::Value, E> {
                Ok(UniqueValue(value.into()))
            }
            fn visit_u64<E: serde::de::Error>(self, value: u64) -> Result<Self::Value, E> {
                Ok(UniqueValue(value.into()))
            }
            fn visit_f64<E: serde::de::Error>(self, value: f64) -> Result<Self::Value, E> {
                serde_json::Number::from_f64(value)
                    .map(|number| UniqueValue(number.into()))
                    .ok_or_else(|| E::custom("nonfinite CPU record number"))
            }
            fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Self::Value, E> {
                Ok(UniqueValue(value.into()))
            }
            fn visit_string<E: serde::de::Error>(self, value: String) -> Result<Self::Value, E> {
                Ok(UniqueValue(value.into()))
            }
            fn visit_unit<E: serde::de::Error>(self) -> Result<Self::Value, E> {
                Ok(UniqueValue(serde_json::Value::Null))
            }
        }
        deserializer.deserialize_any(Visitor)
    }
}

fn same_original_fence(original: &File, probe: &File) -> io::Result<bool> {
    let original_meta = original.metadata()?;
    let probe_meta = probe.metadata()?;
    if (original_meta.dev(), original_meta.ino()) != (probe_meta.dev(), probe_meta.ino()) {
        return Ok(false);
    }
    // A separate description already observed this exact inode held EX.
    // Reassert only on the supplied original description; an independent open
    // cannot satisfy this while the actual exclusive owner remains present.
    Ok(original.try_lock().is_ok())
}

fn open_record(root: &File, name: &str) -> io::Result<File> {
    let file = crate::unix::open_at(root, name, libc::O_RDONLY, false)?;
    let meta = file.metadata()?;
    // SAFETY: geteuid reads this process's effective UID and has no arguments.
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o022 != 0
    {
        return Err(invalid("external CPU record has unsafe ownership or mode"));
    }
    let named = crate::unix::open_at(root, name, libc::O_RDONLY, false)?.metadata()?;
    if (named.dev(), named.ino()) != (meta.dev(), meta.ino()) {
        return Err(invalid("external CPU record changed during observation"));
    }
    Ok(file)
}

fn held(file: &File) -> io::Result<bool> {
    match file.try_lock_shared() {
        Ok(()) => {
            file.unlock()?;
            Ok(false)
        }
        Err(std::fs::TryLockError::WouldBlock) => Ok(true),
        Err(std::fs::TryLockError::Error(error)) => Err(error),
    }
}

#[cfg(test)]
mod tests;
